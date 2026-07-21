#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_119 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_118 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_117 {
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
        case 119:
        case 120:
            return sizeof(struct struct_rec_119);
        case 118:
            return sizeof(struct struct_rec_118);
        case 117:
            return sizeof(struct struct_rec_117);
        case 94:
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
        case 106:
        case 107:
        case 108:
        case 110:
        case 111:
        case 112:
        case 113:
        case 114:
        case 115:
        case 116:
        case 121:
        case 122:
        case 123:
        case 124:
        case 125:
            return sizeof(sisal_array_t);
        case 7:
        case 13:
            return sizeof(int64_t);
        case 2:
        case 6:
        case 10:
        case 109:
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

extern "C" sisal_array_t func_FI_GATHER_BODY_TEMP(int32_t N);
extern "C" sisal_array_t func_FI_GATHER_ZERO(int32_t N);
extern "C" sisal_array_t func_FI_PARAM_BUMP(int32_t N, sisal_array_t AIN);
extern "C" sisal_array_t func_FI_PARAM_IDENTITY(int32_t N, sisal_array_t AIN);
extern "C" int32_t func_FI_FIB_A(int32_t N);
extern "C" int32_t func_FI_FIB(int32_t N);
extern "C" int32_t func_FI_SWAP(int32_t N);
extern "C" int32_t func_FI_PASSTHRU(int32_t N);
extern "C" int32_t func_FI_FINAL_I(int32_t N);
extern "C" int32_t func_FI_PRODUCT(int32_t N);
extern "C" int32_t func_FI_SUM(int32_t N);

extern "C" int32_t func_FI_SUM(int32_t N) {
  int32_t v_g1_n__0_N = 0;
  (v_g1_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g1_n__0_p0_i = 0;
  int32_t v_g1_n__1_p0_o = 0;
  {
    int32_t v_LoopB_20055_n__5_MERGE_I = 0;
    int32_t v_LoopB_20055_n__6_MERGE_S = 0;
    int32_t v_LoopB_20055_n__7_MERGE_OLD_I = 0;
    int32_t v_LoopB_20055_n__8_MERGE_OLD_S = 0;
    bool v_LoopB_20055_n__9_MERGE_first = 0;
    int32_t v_LoopB_20055_bodycap_n2_p0 = 0;
    int32_t v_LoopB_20055_bodycap_n3_p0 = 0;
    bool v_LoopB_20055_bodycap_n4_p0 = 0;
    int32_t v_LoopB_20055_n__0_N = 0;
    (v_LoopB_20055_n__0_N = SISAL_CAST(int32_t, v_g1_n__0_N));
    int32_t v_INIT_20059_n__1_I = 0;
    int32_t v_INIT_20059_n__0_N = 0;
    int32_t v_INIT_20059_n__1_OLD_I = 0;
    int32_t v_INIT_20059_n__2_OLD_S = 0;
    int32_t v_INIT_20059_n__2_S = 0;
    (v_INIT_20059_n__0_N = SISAL_CAST(int32_t, v_LoopB_20055_n__0_N));
    (v_INIT_20059_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_20059_n__2_S = SISAL_CAST(int32_t, 0));
    bool v_INIT_20059_n__3_p0_o = 0;
    (v_INIT_20059_n__3_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_20055_n__5_MERGE_I = v_INIT_20059_n__1_OLD_I);
    (v_LoopB_20055_n__6_MERGE_S = v_INIT_20059_n__2_S);
    (v_LoopB_20055_n__7_MERGE_OLD_I = v_INIT_20059_n__1_OLD_I);
    (v_LoopB_20055_n__8_MERGE_OLD_S = v_INIT_20059_n__2_S);
    (v_LoopB_20055_n__9_MERGE_first = v_INIT_20059_n__3_p0_o);
    int32_t v_TEST_20058_n__0_I = 0;
    int32_t v_TEST_20058_n__0_N = 0;
    int32_t v_TEST_20058_n__0_OLD_I = 0;
    int32_t v_TEST_20058_n__0_OLD_S = 0;
    int32_t v_TEST_20058_n__0_S = 0;
    (v_TEST_20058_n__0_I = SISAL_CAST(int32_t, v_LoopB_20055_n__5_MERGE_I));
    (v_TEST_20058_n__0_N = SISAL_CAST(int32_t, v_LoopB_20055_n__0_N));
    (v_TEST_20058_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_20055_n__7_MERGE_OLD_I));
    (v_TEST_20058_n__0_OLD_S = SISAL_CAST(int32_t, v_LoopB_20055_n__8_MERGE_OLD_S));
    (v_TEST_20058_n__0_S = SISAL_CAST(int32_t, v_LoopB_20055_n__6_MERGE_S));
    bool v_TEST_20058_n__1_p0_o = 0;
    (v_TEST_20058_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_20058_n__0_I) <= SISAL_CAST(int32_t, v_TEST_20058_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_20058_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_20055 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_20058_n__1_p0_o) {
      int32_t v_BODY_20056_n__2_I = 0;
      int32_t v_BODY_20056_n__0_N = 0;
      int32_t v_BODY_20056_n__0_OLD_I = 0;
      int32_t v_BODY_20056_n__0_OLD_S = 0;
      int32_t v_BODY_20056_n__3_S = 0;
      int32_t v_BODY_20056_n__0_p0_o = 0;
      (v_BODY_20056_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_20055_n__5_MERGE_I));
      (v_BODY_20056_n__0_N = SISAL_CAST(int32_t, v_LoopB_20055_n__0_N));
      (v_BODY_20056_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_20055_n__7_MERGE_OLD_I));
      (v_BODY_20056_n__0_OLD_S = SISAL_CAST(int32_t, v_LoopB_20055_n__8_MERGE_OLD_S));
      int32_t v_BODY_20056_n__0_p4_o = 0;
      (v_BODY_20056_n__0_p4_o = SISAL_CAST(int32_t, v_LoopB_20055_n__6_MERGE_S));
      int32_t v_BODY_20056_n__1_p0_o = 0;
      (v_BODY_20056_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_20056_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_20056_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_20056_n__1_p0_o))));
      (v_BODY_20056_n__3_S = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_20056_n__0_OLD_S) + SISAL_CAST(int32_t, v_BODY_20056_n__0_OLD_I))));
      bool v_BODY_20056_n__4_p0_o = 0;
      (v_BODY_20056_n__4_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_20055_bodycap_n2_p0 = v_BODY_20056_n__2_I);
      (v_LoopB_20055_bodycap_n3_p0 = v_BODY_20056_n__3_S);
      (v_LoopB_20055_bodycap_n4_p0 = v_BODY_20056_n__4_p0_o);
      (v_LoopB_20055_n__5_MERGE_I = v_LoopB_20055_bodycap_n2_p0);
      (v_LoopB_20055_n__6_MERGE_S = v_LoopB_20055_bodycap_n3_p0);
      (v_LoopB_20055_n__7_MERGE_OLD_I = v_LoopB_20055_bodycap_n2_p0);
      (v_LoopB_20055_n__8_MERGE_OLD_S = v_LoopB_20055_bodycap_n3_p0);
      (v_LoopB_20055_n__9_MERGE_first = v_LoopB_20055_bodycap_n4_p0);
      (v_TEST_20058_n__0_I = SISAL_CAST(int32_t, v_LoopB_20055_n__5_MERGE_I));
      (v_TEST_20058_n__0_N = SISAL_CAST(int32_t, v_LoopB_20055_n__0_N));
      (v_TEST_20058_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_20055_n__7_MERGE_OLD_I));
      (v_TEST_20058_n__0_OLD_S = SISAL_CAST(int32_t, v_LoopB_20055_n__8_MERGE_OLD_S));
      (v_TEST_20058_n__0_S = SISAL_CAST(int32_t, v_LoopB_20055_n__6_MERGE_S));
      (v_TEST_20058_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_20058_n__0_I) <= SISAL_CAST(int32_t, v_TEST_20058_n__0_N))));
    }
    int32_t v_RETURNS_20057_n__0_p0_o = 0;
    (v_RETURNS_20057_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_20055_n__8_MERGE_OLD_S));
    int32_t v_RETURNS_20057_n__1_p0_o = 0;
    (v_RETURNS_20057_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_20057_n__0_p0_o)));
    (v_g1_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_20057_n__1_p0_o));
  }
  (v_g1_n__0_p0_i = SISAL_CAST(int32_t, v_g1_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g1_n__0_p0_i);
}

extern "C" int32_t func_FI_PRODUCT(int32_t N) {
  int32_t v_g2_n__0_N = 0;
  (v_g2_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g2_n__0_p0_i = 0;
  int32_t v_g2_n__1_p0_o = 0;
  {
    int32_t v_LoopB_19050_n__5_MERGE_I = 0;
    int32_t v_LoopB_19050_n__6_MERGE_P = 0;
    int32_t v_LoopB_19050_n__7_MERGE_OLD_I = 0;
    int32_t v_LoopB_19050_n__8_MERGE_OLD_P = 0;
    bool v_LoopB_19050_n__9_MERGE_first = 0;
    int32_t v_LoopB_19050_bodycap_n2_p0 = 0;
    int32_t v_LoopB_19050_bodycap_n3_p0 = 0;
    bool v_LoopB_19050_bodycap_n4_p0 = 0;
    int32_t v_LoopB_19050_n__0_N = 0;
    (v_LoopB_19050_n__0_N = SISAL_CAST(int32_t, v_g2_n__0_N));
    int32_t v_INIT_19054_n__1_I = 0;
    int32_t v_INIT_19054_n__0_N = 0;
    int32_t v_INIT_19054_n__1_OLD_I = 0;
    int32_t v_INIT_19054_n__2_OLD_P = 0;
    int32_t v_INIT_19054_n__2_P = 0;
    (v_INIT_19054_n__0_N = SISAL_CAST(int32_t, v_LoopB_19050_n__0_N));
    (v_INIT_19054_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_19054_n__2_P = SISAL_CAST(int32_t, 1));
    bool v_INIT_19054_n__3_p0_o = 0;
    (v_INIT_19054_n__3_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_19050_n__5_MERGE_I = v_INIT_19054_n__1_OLD_I);
    (v_LoopB_19050_n__6_MERGE_P = v_INIT_19054_n__2_P);
    (v_LoopB_19050_n__7_MERGE_OLD_I = v_INIT_19054_n__1_OLD_I);
    (v_LoopB_19050_n__8_MERGE_OLD_P = v_INIT_19054_n__2_P);
    (v_LoopB_19050_n__9_MERGE_first = v_INIT_19054_n__3_p0_o);
    int32_t v_TEST_19053_n__0_I = 0;
    int32_t v_TEST_19053_n__0_N = 0;
    int32_t v_TEST_19053_n__0_OLD_I = 0;
    int32_t v_TEST_19053_n__0_OLD_P = 0;
    int32_t v_TEST_19053_n__0_P = 0;
    (v_TEST_19053_n__0_I = SISAL_CAST(int32_t, v_LoopB_19050_n__5_MERGE_I));
    (v_TEST_19053_n__0_N = SISAL_CAST(int32_t, v_LoopB_19050_n__0_N));
    (v_TEST_19053_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_19050_n__7_MERGE_OLD_I));
    (v_TEST_19053_n__0_OLD_P = SISAL_CAST(int32_t, v_LoopB_19050_n__8_MERGE_OLD_P));
    (v_TEST_19053_n__0_P = SISAL_CAST(int32_t, v_LoopB_19050_n__6_MERGE_P));
    bool v_TEST_19053_n__1_p0_o = 0;
    (v_TEST_19053_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_19053_n__0_I) <= SISAL_CAST(int32_t, v_TEST_19053_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_19053_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_19050 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_19053_n__1_p0_o) {
      int32_t v_BODY_19051_n__2_I = 0;
      int32_t v_BODY_19051_n__0_N = 0;
      int32_t v_BODY_19051_n__0_OLD_I = 0;
      int32_t v_BODY_19051_n__0_OLD_P = 0;
      int32_t v_BODY_19051_n__3_P = 0;
      int32_t v_BODY_19051_n__0_p0_o = 0;
      (v_BODY_19051_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_19050_n__5_MERGE_I));
      (v_BODY_19051_n__0_N = SISAL_CAST(int32_t, v_LoopB_19050_n__0_N));
      (v_BODY_19051_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_19050_n__7_MERGE_OLD_I));
      (v_BODY_19051_n__0_OLD_P = SISAL_CAST(int32_t, v_LoopB_19050_n__8_MERGE_OLD_P));
      int32_t v_BODY_19051_n__0_p4_o = 0;
      (v_BODY_19051_n__0_p4_o = SISAL_CAST(int32_t, v_LoopB_19050_n__6_MERGE_P));
      int32_t v_BODY_19051_n__1_p0_o = 0;
      (v_BODY_19051_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_19051_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_19051_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_19051_n__1_p0_o))));
      (v_BODY_19051_n__3_P = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_19051_n__0_OLD_P) * SISAL_CAST(int32_t, v_BODY_19051_n__0_OLD_I))));
      bool v_BODY_19051_n__4_p0_o = 0;
      (v_BODY_19051_n__4_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_19050_bodycap_n2_p0 = v_BODY_19051_n__2_I);
      (v_LoopB_19050_bodycap_n3_p0 = v_BODY_19051_n__3_P);
      (v_LoopB_19050_bodycap_n4_p0 = v_BODY_19051_n__4_p0_o);
      (v_LoopB_19050_n__5_MERGE_I = v_LoopB_19050_bodycap_n2_p0);
      (v_LoopB_19050_n__6_MERGE_P = v_LoopB_19050_bodycap_n3_p0);
      (v_LoopB_19050_n__7_MERGE_OLD_I = v_LoopB_19050_bodycap_n2_p0);
      (v_LoopB_19050_n__8_MERGE_OLD_P = v_LoopB_19050_bodycap_n3_p0);
      (v_LoopB_19050_n__9_MERGE_first = v_LoopB_19050_bodycap_n4_p0);
      (v_TEST_19053_n__0_I = SISAL_CAST(int32_t, v_LoopB_19050_n__5_MERGE_I));
      (v_TEST_19053_n__0_N = SISAL_CAST(int32_t, v_LoopB_19050_n__0_N));
      (v_TEST_19053_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_19050_n__7_MERGE_OLD_I));
      (v_TEST_19053_n__0_OLD_P = SISAL_CAST(int32_t, v_LoopB_19050_n__8_MERGE_OLD_P));
      (v_TEST_19053_n__0_P = SISAL_CAST(int32_t, v_LoopB_19050_n__6_MERGE_P));
      (v_TEST_19053_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_19053_n__0_I) <= SISAL_CAST(int32_t, v_TEST_19053_n__0_N))));
    }
    int32_t v_RETURNS_19052_n__0_p0_o = 0;
    (v_RETURNS_19052_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_19050_n__8_MERGE_OLD_P));
    int32_t v_RETURNS_19052_n__1_p0_o = 0;
    (v_RETURNS_19052_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_19052_n__0_p0_o)));
    (v_g2_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_19052_n__1_p0_o));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(int32_t, v_g2_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g2_n__0_p0_i);
}

extern "C" int32_t func_FI_FINAL_I(int32_t N) {
  int32_t v_g3_n__0_N = 0;
  (v_g3_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g3_n__0_p0_i = 0;
  int32_t v_g3_n__1_p0_o = 0;
  {
    int32_t v_LoopB_18045_n__5_MERGE_I = 0;
    int32_t v_LoopB_18045_n__6_MERGE_OLD_I = 0;
    bool v_LoopB_18045_n__7_MERGE_first = 0;
    int32_t v_LoopB_18045_bodycap_n2_p0 = 0;
    bool v_LoopB_18045_bodycap_n3_p0 = 0;
    int32_t v_LoopB_18045_n__0_N = 0;
    (v_LoopB_18045_n__0_N = SISAL_CAST(int32_t, v_g3_n__0_N));
    int32_t v_INIT_18049_n__1_I = 0;
    int32_t v_INIT_18049_n__0_N = 0;
    int32_t v_INIT_18049_n__1_OLD_I = 0;
    (v_INIT_18049_n__0_N = SISAL_CAST(int32_t, v_LoopB_18045_n__0_N));
    (v_INIT_18049_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    bool v_INIT_18049_n__2_p0_o = 0;
    (v_INIT_18049_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_18045_n__5_MERGE_I = v_INIT_18049_n__1_OLD_I);
    (v_LoopB_18045_n__6_MERGE_OLD_I = v_INIT_18049_n__1_OLD_I);
    (v_LoopB_18045_n__7_MERGE_first = v_INIT_18049_n__2_p0_o);
    int32_t v_TEST_18048_n__0_I = 0;
    int32_t v_TEST_18048_n__0_N = 0;
    int32_t v_TEST_18048_n__0_OLD_I = 0;
    (v_TEST_18048_n__0_I = SISAL_CAST(int32_t, v_LoopB_18045_n__5_MERGE_I));
    (v_TEST_18048_n__0_N = SISAL_CAST(int32_t, v_LoopB_18045_n__0_N));
    (v_TEST_18048_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_18045_n__6_MERGE_OLD_I));
    bool v_TEST_18048_n__1_p0_o = 0;
    (v_TEST_18048_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_18048_n__0_I) <= SISAL_CAST(int32_t, v_TEST_18048_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_18048_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_18045 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_18048_n__1_p0_o) {
      int32_t v_BODY_18046_n__2_I = 0;
      int32_t v_BODY_18046_n__0_N = 0;
      int32_t v_BODY_18046_n__0_OLD_I = 0;
      int32_t v_BODY_18046_n__0_p0_o = 0;
      (v_BODY_18046_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_18045_n__5_MERGE_I));
      (v_BODY_18046_n__0_N = SISAL_CAST(int32_t, v_LoopB_18045_n__0_N));
      (v_BODY_18046_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_18045_n__6_MERGE_OLD_I));
      int32_t v_BODY_18046_n__1_p0_o = 0;
      (v_BODY_18046_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_18046_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_18046_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_18046_n__1_p0_o))));
      bool v_BODY_18046_n__3_p0_o = 0;
      (v_BODY_18046_n__3_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_18045_bodycap_n2_p0 = v_BODY_18046_n__2_I);
      (v_LoopB_18045_bodycap_n3_p0 = v_BODY_18046_n__3_p0_o);
      (v_LoopB_18045_n__5_MERGE_I = v_LoopB_18045_bodycap_n2_p0);
      (v_LoopB_18045_n__6_MERGE_OLD_I = v_LoopB_18045_bodycap_n2_p0);
      (v_LoopB_18045_n__7_MERGE_first = v_LoopB_18045_bodycap_n3_p0);
      (v_TEST_18048_n__0_I = SISAL_CAST(int32_t, v_LoopB_18045_n__5_MERGE_I));
      (v_TEST_18048_n__0_N = SISAL_CAST(int32_t, v_LoopB_18045_n__0_N));
      (v_TEST_18048_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_18045_n__6_MERGE_OLD_I));
      (v_TEST_18048_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_18048_n__0_I) <= SISAL_CAST(int32_t, v_TEST_18048_n__0_N))));
    }
    int32_t v_RETURNS_18047_n__0_p0_o = 0;
    (v_RETURNS_18047_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_18045_n__6_MERGE_OLD_I));
    int32_t v_RETURNS_18047_n__1_p0_o = 0;
    (v_RETURNS_18047_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_18047_n__0_p0_o)));
    (v_g3_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_18047_n__1_p0_o));
  }
  (v_g3_n__0_p0_i = SISAL_CAST(int32_t, v_g3_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g3_n__0_p0_i);
}

extern "C" int32_t func_FI_PASSTHRU(int32_t N) {
  int32_t v_g4_n__0_N = 0;
  (v_g4_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g4_n__0_p0_i = 0;
  int32_t v_g4_n__1_p0_o = 0;
  {
    int32_t v_LoopB_17040_n__5_MERGE_I = 0;
    int32_t v_LoopB_17040_n__6_MERGE_K = 0;
    int32_t v_LoopB_17040_n__7_MERGE_OLD_I = 0;
    int32_t v_LoopB_17040_n__8_MERGE_OLD_K = 0;
    bool v_LoopB_17040_n__9_MERGE_first = 0;
    int32_t v_LoopB_17040_bodycap_n0_p4 = 0;
    int32_t v_LoopB_17040_bodycap_n2_p0 = 0;
    bool v_LoopB_17040_bodycap_n3_p0 = 0;
    int32_t v_LoopB_17040_n__0_N = 0;
    (v_LoopB_17040_n__0_N = SISAL_CAST(int32_t, v_g4_n__0_N));
    int32_t v_INIT_17044_n__1_I = 0;
    int32_t v_INIT_17044_n__2_K = 0;
    int32_t v_INIT_17044_n__0_N = 0;
    int32_t v_INIT_17044_n__1_OLD_I = 0;
    int32_t v_INIT_17044_n__2_OLD_K = 0;
    (v_INIT_17044_n__0_N = SISAL_CAST(int32_t, v_LoopB_17040_n__0_N));
    (v_INIT_17044_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_17044_n__2_OLD_K = SISAL_CAST(int32_t, 42));
    bool v_INIT_17044_n__3_p0_o = 0;
    (v_INIT_17044_n__3_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_17040_n__5_MERGE_I = v_INIT_17044_n__1_OLD_I);
    (v_LoopB_17040_n__6_MERGE_K = v_INIT_17044_n__2_OLD_K);
    (v_LoopB_17040_n__7_MERGE_OLD_I = v_INIT_17044_n__1_OLD_I);
    (v_LoopB_17040_n__8_MERGE_OLD_K = v_INIT_17044_n__2_OLD_K);
    (v_LoopB_17040_n__9_MERGE_first = v_INIT_17044_n__3_p0_o);
    int32_t v_TEST_17043_n__0_I = 0;
    int32_t v_TEST_17043_n__0_K = 0;
    int32_t v_TEST_17043_n__0_N = 0;
    int32_t v_TEST_17043_n__0_OLD_I = 0;
    int32_t v_TEST_17043_n__0_OLD_K = 0;
    (v_TEST_17043_n__0_I = SISAL_CAST(int32_t, v_LoopB_17040_n__5_MERGE_I));
    (v_TEST_17043_n__0_K = SISAL_CAST(int32_t, v_LoopB_17040_n__6_MERGE_K));
    (v_TEST_17043_n__0_N = SISAL_CAST(int32_t, v_LoopB_17040_n__0_N));
    (v_TEST_17043_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_17040_n__7_MERGE_OLD_I));
    (v_TEST_17043_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_17040_n__8_MERGE_OLD_K));
    bool v_TEST_17043_n__1_p0_o = 0;
    (v_TEST_17043_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_17043_n__0_I) <= SISAL_CAST(int32_t, v_TEST_17043_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_17043_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_17040 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_17043_n__1_p0_o) {
      int32_t v_BODY_17041_n__2_I = 0;
      int32_t v_BODY_17041_n__0_K = 0;
      int32_t v_BODY_17041_n__0_N = 0;
      int32_t v_BODY_17041_n__0_OLD_I = 0;
      int32_t v_BODY_17041_n__0_OLD_K = 0;
      int32_t v_BODY_17041_n__0_p0_o = 0;
      (v_BODY_17041_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_17040_n__5_MERGE_I));
      int32_t v_BODY_17041_n__0_p1_o = 0;
      (v_BODY_17041_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_17040_n__6_MERGE_K));
      (v_BODY_17041_n__0_N = SISAL_CAST(int32_t, v_LoopB_17040_n__0_N));
      (v_BODY_17041_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_17040_n__7_MERGE_OLD_I));
      (v_BODY_17041_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_17040_n__8_MERGE_OLD_K));
      int32_t v_BODY_17041_n__1_p0_o = 0;
      (v_BODY_17041_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_17041_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_17041_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_17041_n__1_p0_o))));
      bool v_BODY_17041_n__3_p0_o = 0;
      (v_BODY_17041_n__3_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_17040_bodycap_n0_p4 = v_BODY_17041_n__0_OLD_K);
      (v_LoopB_17040_bodycap_n2_p0 = v_BODY_17041_n__2_I);
      (v_LoopB_17040_bodycap_n3_p0 = v_BODY_17041_n__3_p0_o);
      (v_LoopB_17040_n__5_MERGE_I = v_LoopB_17040_bodycap_n2_p0);
      (v_LoopB_17040_n__6_MERGE_K = v_LoopB_17040_bodycap_n0_p4);
      (v_LoopB_17040_n__7_MERGE_OLD_I = v_LoopB_17040_bodycap_n2_p0);
      (v_LoopB_17040_n__8_MERGE_OLD_K = v_LoopB_17040_bodycap_n0_p4);
      (v_LoopB_17040_n__9_MERGE_first = v_LoopB_17040_bodycap_n3_p0);
      (v_TEST_17043_n__0_I = SISAL_CAST(int32_t, v_LoopB_17040_n__5_MERGE_I));
      (v_TEST_17043_n__0_K = SISAL_CAST(int32_t, v_LoopB_17040_n__6_MERGE_K));
      (v_TEST_17043_n__0_N = SISAL_CAST(int32_t, v_LoopB_17040_n__0_N));
      (v_TEST_17043_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_17040_n__7_MERGE_OLD_I));
      (v_TEST_17043_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_17040_n__8_MERGE_OLD_K));
      (v_TEST_17043_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_17043_n__0_I) <= SISAL_CAST(int32_t, v_TEST_17043_n__0_N))));
    }
    int32_t v_RETURNS_17042_n__0_p0_o = 0;
    (v_RETURNS_17042_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_17040_n__8_MERGE_OLD_K));
    int32_t v_RETURNS_17042_n__1_p0_o = 0;
    (v_RETURNS_17042_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_17042_n__0_p0_o)));
    (v_g4_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_17042_n__1_p0_o));
  }
  (v_g4_n__0_p0_i = SISAL_CAST(int32_t, v_g4_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g4_n__0_p0_i);
}

extern "C" int32_t func_FI_SWAP(int32_t N) {
  int32_t v_g5_n__0_N = 0;
  (v_g5_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g5_n__0_p0_i = 0;
  int32_t v_g5_n__1_p0_o = 0;
  {
    int32_t v_LoopB_16035_n__5_MERGE_A = 0;
    int32_t v_LoopB_16035_n__6_MERGE_B = 0;
    int32_t v_LoopB_16035_n__7_MERGE_I = 0;
    int32_t v_LoopB_16035_n__8_MERGE_OLD_A = 0;
    int32_t v_LoopB_16035_n__9_MERGE_OLD_B = 0;
    int32_t v_LoopB_16035_n__10_MERGE_OLD_I = 0;
    bool v_LoopB_16035_n__11_MERGE_first = 0;
    int32_t v_LoopB_16035_bodycap_n0_p4 = 0;
    int32_t v_LoopB_16035_bodycap_n0_p5 = 0;
    int32_t v_LoopB_16035_bodycap_n2_p0 = 0;
    bool v_LoopB_16035_bodycap_n3_p0 = 0;
    int32_t v_LoopB_16035_n__0_N = 0;
    (v_LoopB_16035_n__0_N = SISAL_CAST(int32_t, v_g5_n__0_N));
    int32_t v_INIT_16039_n__2_A = 0;
    int32_t v_INIT_16039_n__3_B = 0;
    int32_t v_INIT_16039_n__1_I = 0;
    int32_t v_INIT_16039_n__0_N = 0;
    int32_t v_INIT_16039_n__2_OLD_A = 0;
    int32_t v_INIT_16039_n__3_OLD_B = 0;
    int32_t v_INIT_16039_n__1_OLD_I = 0;
    (v_INIT_16039_n__0_N = SISAL_CAST(int32_t, v_LoopB_16035_n__0_N));
    (v_INIT_16039_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_16039_n__2_OLD_A = SISAL_CAST(int32_t, 10));
    (v_INIT_16039_n__3_OLD_B = SISAL_CAST(int32_t, 20));
    bool v_INIT_16039_n__4_p0_o = 0;
    (v_INIT_16039_n__4_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_16035_n__5_MERGE_A = v_INIT_16039_n__2_OLD_A);
    (v_LoopB_16035_n__6_MERGE_B = v_INIT_16039_n__3_OLD_B);
    (v_LoopB_16035_n__7_MERGE_I = v_INIT_16039_n__1_OLD_I);
    (v_LoopB_16035_n__8_MERGE_OLD_A = v_INIT_16039_n__2_OLD_A);
    (v_LoopB_16035_n__9_MERGE_OLD_B = v_INIT_16039_n__3_OLD_B);
    (v_LoopB_16035_n__10_MERGE_OLD_I = v_INIT_16039_n__1_OLD_I);
    (v_LoopB_16035_n__11_MERGE_first = v_INIT_16039_n__4_p0_o);
    int32_t v_TEST_16038_n__0_A = 0;
    int32_t v_TEST_16038_n__0_B = 0;
    int32_t v_TEST_16038_n__0_I = 0;
    int32_t v_TEST_16038_n__0_N = 0;
    int32_t v_TEST_16038_n__0_OLD_A = 0;
    int32_t v_TEST_16038_n__0_OLD_B = 0;
    int32_t v_TEST_16038_n__0_OLD_I = 0;
    (v_TEST_16038_n__0_A = SISAL_CAST(int32_t, v_LoopB_16035_n__5_MERGE_A));
    (v_TEST_16038_n__0_B = SISAL_CAST(int32_t, v_LoopB_16035_n__6_MERGE_B));
    (v_TEST_16038_n__0_I = SISAL_CAST(int32_t, v_LoopB_16035_n__7_MERGE_I));
    (v_TEST_16038_n__0_N = SISAL_CAST(int32_t, v_LoopB_16035_n__0_N));
    (v_TEST_16038_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopB_16035_n__8_MERGE_OLD_A));
    (v_TEST_16038_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopB_16035_n__9_MERGE_OLD_B));
    (v_TEST_16038_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_16035_n__10_MERGE_OLD_I));
    bool v_TEST_16038_n__1_p0_o = 0;
    (v_TEST_16038_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_16038_n__0_I) <= SISAL_CAST(int32_t, v_TEST_16038_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_16038_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_16035 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_16038_n__1_p0_o) {
      int32_t v_BODY_16036_n__0_A = 0;
      int32_t v_BODY_16036_n__0_B = 0;
      int32_t v_BODY_16036_n__2_I = 0;
      int32_t v_BODY_16036_n__0_N = 0;
      int32_t v_BODY_16036_n__0_OLD_A = 0;
      int32_t v_BODY_16036_n__0_OLD_B = 0;
      int32_t v_BODY_16036_n__0_OLD_I = 0;
      int32_t v_BODY_16036_n__0_p0_o = 0;
      (v_BODY_16036_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_16035_n__5_MERGE_A));
      int32_t v_BODY_16036_n__0_p1_o = 0;
      (v_BODY_16036_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_16035_n__6_MERGE_B));
      int32_t v_BODY_16036_n__0_p2_o = 0;
      (v_BODY_16036_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_16035_n__7_MERGE_I));
      (v_BODY_16036_n__0_N = SISAL_CAST(int32_t, v_LoopB_16035_n__0_N));
      (v_BODY_16036_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopB_16035_n__8_MERGE_OLD_A));
      (v_BODY_16036_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopB_16035_n__9_MERGE_OLD_B));
      (v_BODY_16036_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_16035_n__10_MERGE_OLD_I));
      int32_t v_BODY_16036_n__1_p0_o = 0;
      (v_BODY_16036_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_16036_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_16036_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_16036_n__1_p0_o))));
      bool v_BODY_16036_n__3_p0_o = 0;
      (v_BODY_16036_n__3_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_16035_bodycap_n0_p4 = v_BODY_16036_n__0_OLD_A);
      (v_LoopB_16035_bodycap_n0_p5 = v_BODY_16036_n__0_OLD_B);
      (v_LoopB_16035_bodycap_n2_p0 = v_BODY_16036_n__2_I);
      (v_LoopB_16035_bodycap_n3_p0 = v_BODY_16036_n__3_p0_o);
      (v_LoopB_16035_n__5_MERGE_A = v_LoopB_16035_bodycap_n0_p5);
      (v_LoopB_16035_n__6_MERGE_B = v_LoopB_16035_bodycap_n0_p4);
      (v_LoopB_16035_n__7_MERGE_I = v_LoopB_16035_bodycap_n2_p0);
      (v_LoopB_16035_n__8_MERGE_OLD_A = v_LoopB_16035_bodycap_n0_p5);
      (v_LoopB_16035_n__9_MERGE_OLD_B = v_LoopB_16035_bodycap_n0_p4);
      (v_LoopB_16035_n__10_MERGE_OLD_I = v_LoopB_16035_bodycap_n2_p0);
      (v_LoopB_16035_n__11_MERGE_first = v_LoopB_16035_bodycap_n3_p0);
      (v_TEST_16038_n__0_A = SISAL_CAST(int32_t, v_LoopB_16035_n__5_MERGE_A));
      (v_TEST_16038_n__0_B = SISAL_CAST(int32_t, v_LoopB_16035_n__6_MERGE_B));
      (v_TEST_16038_n__0_I = SISAL_CAST(int32_t, v_LoopB_16035_n__7_MERGE_I));
      (v_TEST_16038_n__0_N = SISAL_CAST(int32_t, v_LoopB_16035_n__0_N));
      (v_TEST_16038_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopB_16035_n__8_MERGE_OLD_A));
      (v_TEST_16038_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopB_16035_n__9_MERGE_OLD_B));
      (v_TEST_16038_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_16035_n__10_MERGE_OLD_I));
      (v_TEST_16038_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_16038_n__0_I) <= SISAL_CAST(int32_t, v_TEST_16038_n__0_N))));
    }
    int32_t v_RETURNS_16037_n__0_p0_o = 0;
    (v_RETURNS_16037_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_16035_n__8_MERGE_OLD_A));
    int32_t v_RETURNS_16037_n__1_p0_o = 0;
    (v_RETURNS_16037_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_16037_n__0_p0_o)));
    (v_g5_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_16037_n__1_p0_o));
  }
  (v_g5_n__0_p0_i = SISAL_CAST(int32_t, v_g5_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g5_n__0_p0_i);
}

extern "C" int32_t func_FI_FIB(int32_t N) {
  int32_t v_g6_n__0_N = 0;
  (v_g6_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g6_n__0_p0_i = 0;
  int32_t v_g6_n__1_p0_o = 0;
  {
    int32_t v_LoopB_15030_n__5_MERGE_A = 0;
    int32_t v_LoopB_15030_n__6_MERGE_B = 0;
    int32_t v_LoopB_15030_n__7_MERGE_I = 0;
    int32_t v_LoopB_15030_n__8_MERGE_OLD_A = 0;
    int32_t v_LoopB_15030_n__9_MERGE_OLD_B = 0;
    int32_t v_LoopB_15030_n__10_MERGE_OLD_I = 0;
    bool v_LoopB_15030_n__11_MERGE_first = 0;
    int32_t v_LoopB_15030_bodycap_n0_p5 = 0;
    int32_t v_LoopB_15030_bodycap_n2_p0 = 0;
    int32_t v_LoopB_15030_bodycap_n3_p0 = 0;
    bool v_LoopB_15030_bodycap_n4_p0 = 0;
    int32_t v_LoopB_15030_n__0_N = 0;
    (v_LoopB_15030_n__0_N = SISAL_CAST(int32_t, v_g6_n__0_N));
    int32_t v_INIT_15034_n__2_A = 0;
    int32_t v_INIT_15034_n__3_B = 0;
    int32_t v_INIT_15034_n__1_I = 0;
    int32_t v_INIT_15034_n__0_N = 0;
    int32_t v_INIT_15034_n__2_OLD_A = 0;
    int32_t v_INIT_15034_n__3_OLD_B = 0;
    int32_t v_INIT_15034_n__1_OLD_I = 0;
    (v_INIT_15034_n__0_N = SISAL_CAST(int32_t, v_LoopB_15030_n__0_N));
    (v_INIT_15034_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_15034_n__2_OLD_A = SISAL_CAST(int32_t, 0));
    (v_INIT_15034_n__3_OLD_B = SISAL_CAST(int32_t, 1));
    bool v_INIT_15034_n__4_p0_o = 0;
    (v_INIT_15034_n__4_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_15030_n__5_MERGE_A = v_INIT_15034_n__2_OLD_A);
    (v_LoopB_15030_n__6_MERGE_B = v_INIT_15034_n__3_OLD_B);
    (v_LoopB_15030_n__7_MERGE_I = v_INIT_15034_n__1_OLD_I);
    (v_LoopB_15030_n__8_MERGE_OLD_A = v_INIT_15034_n__2_OLD_A);
    (v_LoopB_15030_n__9_MERGE_OLD_B = v_INIT_15034_n__3_OLD_B);
    (v_LoopB_15030_n__10_MERGE_OLD_I = v_INIT_15034_n__1_OLD_I);
    (v_LoopB_15030_n__11_MERGE_first = v_INIT_15034_n__4_p0_o);
    int32_t v_TEST_15033_n__0_A = 0;
    int32_t v_TEST_15033_n__0_B = 0;
    int32_t v_TEST_15033_n__0_I = 0;
    int32_t v_TEST_15033_n__0_N = 0;
    int32_t v_TEST_15033_n__0_OLD_A = 0;
    int32_t v_TEST_15033_n__0_OLD_B = 0;
    int32_t v_TEST_15033_n__0_OLD_I = 0;
    (v_TEST_15033_n__0_A = SISAL_CAST(int32_t, v_LoopB_15030_n__5_MERGE_A));
    (v_TEST_15033_n__0_B = SISAL_CAST(int32_t, v_LoopB_15030_n__6_MERGE_B));
    (v_TEST_15033_n__0_I = SISAL_CAST(int32_t, v_LoopB_15030_n__7_MERGE_I));
    (v_TEST_15033_n__0_N = SISAL_CAST(int32_t, v_LoopB_15030_n__0_N));
    (v_TEST_15033_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopB_15030_n__8_MERGE_OLD_A));
    (v_TEST_15033_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopB_15030_n__9_MERGE_OLD_B));
    (v_TEST_15033_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_15030_n__10_MERGE_OLD_I));
    bool v_TEST_15033_n__1_p0_o = 0;
    (v_TEST_15033_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_15033_n__0_I) <= SISAL_CAST(int32_t, v_TEST_15033_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_15033_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_15030 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_15033_n__1_p0_o) {
      int32_t v_BODY_15031_n__0_A = 0;
      int32_t v_BODY_15031_n__3_B = 0;
      int32_t v_BODY_15031_n__2_I = 0;
      int32_t v_BODY_15031_n__0_N = 0;
      int32_t v_BODY_15031_n__0_OLD_A = 0;
      int32_t v_BODY_15031_n__0_OLD_B = 0;
      int32_t v_BODY_15031_n__0_OLD_I = 0;
      int32_t v_BODY_15031_n__0_p0_o = 0;
      (v_BODY_15031_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_15030_n__5_MERGE_A));
      int32_t v_BODY_15031_n__0_p1_o = 0;
      (v_BODY_15031_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_15030_n__6_MERGE_B));
      int32_t v_BODY_15031_n__0_p2_o = 0;
      (v_BODY_15031_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_15030_n__7_MERGE_I));
      (v_BODY_15031_n__0_N = SISAL_CAST(int32_t, v_LoopB_15030_n__0_N));
      (v_BODY_15031_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopB_15030_n__8_MERGE_OLD_A));
      (v_BODY_15031_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopB_15030_n__9_MERGE_OLD_B));
      (v_BODY_15031_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_15030_n__10_MERGE_OLD_I));
      int32_t v_BODY_15031_n__1_p0_o = 0;
      (v_BODY_15031_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_15031_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_15031_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_15031_n__1_p0_o))));
      (v_BODY_15031_n__3_B = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_15031_n__0_OLD_A) + SISAL_CAST(int32_t, v_BODY_15031_n__0_OLD_B))));
      bool v_BODY_15031_n__4_p0_o = 0;
      (v_BODY_15031_n__4_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_15030_bodycap_n0_p5 = v_BODY_15031_n__0_OLD_B);
      (v_LoopB_15030_bodycap_n2_p0 = v_BODY_15031_n__2_I);
      (v_LoopB_15030_bodycap_n3_p0 = v_BODY_15031_n__3_B);
      (v_LoopB_15030_bodycap_n4_p0 = v_BODY_15031_n__4_p0_o);
      (v_LoopB_15030_n__5_MERGE_A = v_LoopB_15030_bodycap_n0_p5);
      (v_LoopB_15030_n__6_MERGE_B = v_LoopB_15030_bodycap_n3_p0);
      (v_LoopB_15030_n__7_MERGE_I = v_LoopB_15030_bodycap_n2_p0);
      (v_LoopB_15030_n__8_MERGE_OLD_A = v_LoopB_15030_bodycap_n0_p5);
      (v_LoopB_15030_n__9_MERGE_OLD_B = v_LoopB_15030_bodycap_n3_p0);
      (v_LoopB_15030_n__10_MERGE_OLD_I = v_LoopB_15030_bodycap_n2_p0);
      (v_LoopB_15030_n__11_MERGE_first = v_LoopB_15030_bodycap_n4_p0);
      (v_TEST_15033_n__0_A = SISAL_CAST(int32_t, v_LoopB_15030_n__5_MERGE_A));
      (v_TEST_15033_n__0_B = SISAL_CAST(int32_t, v_LoopB_15030_n__6_MERGE_B));
      (v_TEST_15033_n__0_I = SISAL_CAST(int32_t, v_LoopB_15030_n__7_MERGE_I));
      (v_TEST_15033_n__0_N = SISAL_CAST(int32_t, v_LoopB_15030_n__0_N));
      (v_TEST_15033_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopB_15030_n__8_MERGE_OLD_A));
      (v_TEST_15033_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopB_15030_n__9_MERGE_OLD_B));
      (v_TEST_15033_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_15030_n__10_MERGE_OLD_I));
      (v_TEST_15033_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_15033_n__0_I) <= SISAL_CAST(int32_t, v_TEST_15033_n__0_N))));
    }
    int32_t v_RETURNS_15032_n__0_p0_o = 0;
    (v_RETURNS_15032_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_15030_n__8_MERGE_OLD_A));
    int32_t v_RETURNS_15032_n__1_p0_o = 0;
    (v_RETURNS_15032_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_15032_n__0_p0_o)));
    (v_g6_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_15032_n__1_p0_o));
  }
  (v_g6_n__0_p0_i = SISAL_CAST(int32_t, v_g6_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g6_n__0_p0_i);
}

extern "C" int32_t func_FI_FIB_A(int32_t N) {
  int32_t v_g7_n__0_N = 0;
  (v_g7_n__0_N = SISAL_CAST(int32_t, N));
  int32_t v_g7_n__0_p0_i = 0;
  int32_t v_g7_n__1_p0_o = 0;
  {
    int32_t v_LoopA_14025_n__5_MERGE_A = 0;
    int32_t v_LoopA_14025_n__6_MERGE_B = 0;
    int32_t v_LoopA_14025_n__7_MERGE_I = 0;
    int32_t v_LoopA_14025_n__8_MERGE_OLD_A = 0;
    int32_t v_LoopA_14025_n__9_MERGE_OLD_B = 0;
    int32_t v_LoopA_14025_n__10_MERGE_OLD_I = 0;
    bool v_LoopA_14025_n__11_MERGE_first = 0;
    int32_t v_LoopA_14025_bodycap_n0_p5 = 0;
    int32_t v_LoopA_14025_bodycap_n2_p0 = 0;
    int32_t v_LoopA_14025_bodycap_n3_p0 = 0;
    bool v_LoopA_14025_bodycap_n4_p0 = 0;
    int32_t v_LoopA_14025_n__0_N = 0;
    (v_LoopA_14025_n__0_N = SISAL_CAST(int32_t, v_g7_n__0_N));
    int32_t v_INIT_14029_n__2_A = 0;
    int32_t v_INIT_14029_n__3_B = 0;
    int32_t v_INIT_14029_n__1_I = 0;
    int32_t v_INIT_14029_n__0_N = 0;
    int32_t v_INIT_14029_n__2_OLD_A = 0;
    int32_t v_INIT_14029_n__3_OLD_B = 0;
    int32_t v_INIT_14029_n__1_OLD_I = 0;
    (v_INIT_14029_n__0_N = SISAL_CAST(int32_t, v_LoopA_14025_n__0_N));
    (v_INIT_14029_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_14029_n__2_OLD_A = SISAL_CAST(int32_t, 0));
    (v_INIT_14029_n__3_OLD_B = SISAL_CAST(int32_t, 1));
    bool v_INIT_14029_n__4_p0_o = 0;
    (v_INIT_14029_n__4_p0_o = SISAL_CAST(bool, true));
    (v_LoopA_14025_n__5_MERGE_A = v_INIT_14029_n__2_OLD_A);
    (v_LoopA_14025_n__6_MERGE_B = v_INIT_14029_n__3_OLD_B);
    (v_LoopA_14025_n__7_MERGE_I = v_INIT_14029_n__1_OLD_I);
    (v_LoopA_14025_n__8_MERGE_OLD_A = v_INIT_14029_n__2_OLD_A);
    (v_LoopA_14025_n__9_MERGE_OLD_B = v_INIT_14029_n__3_OLD_B);
    (v_LoopA_14025_n__10_MERGE_OLD_I = v_INIT_14029_n__1_OLD_I);
    (v_LoopA_14025_n__11_MERGE_first = v_INIT_14029_n__4_p0_o);
    int32_t v_TEST_14028_n__0_A = 0;
    int32_t v_TEST_14028_n__0_B = 0;
    int32_t v_TEST_14028_n__0_I = 0;
    int32_t v_TEST_14028_n__0_N = 0;
    int32_t v_TEST_14028_n__0_OLD_A = 0;
    int32_t v_TEST_14028_n__0_OLD_B = 0;
    int32_t v_TEST_14028_n__0_OLD_I = 0;
    (v_TEST_14028_n__0_N = SISAL_CAST(int32_t, v_LoopA_14025_n__0_N));
    bool v_TEST_14028_n__1_p0_o = 0;
    (v_TEST_14028_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_14028_n__0_I) > SISAL_CAST(int32_t, v_TEST_14028_n__0_N))));
    bool v_TEST_14028_n__3_p0_o = 0;
    (v_TEST_14028_n__3_p0_o = SISAL_CAST(bool, (!SISAL_CAST(bool, v_TEST_14028_n__1_p0_o))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_14028_n__3_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopA_14025 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_14028_n__3_p0_o) {
      int32_t v_BODY_14026_n__0_A = 0;
      int32_t v_BODY_14026_n__3_B = 0;
      int32_t v_BODY_14026_n__2_I = 0;
      int32_t v_BODY_14026_n__0_N = 0;
      int32_t v_BODY_14026_n__0_OLD_A = 0;
      int32_t v_BODY_14026_n__0_OLD_B = 0;
      int32_t v_BODY_14026_n__0_OLD_I = 0;
      int32_t v_BODY_14026_n__0_p0_o = 0;
      (v_BODY_14026_n__0_p0_o = SISAL_CAST(int32_t, v_LoopA_14025_n__5_MERGE_A));
      int32_t v_BODY_14026_n__0_p1_o = 0;
      (v_BODY_14026_n__0_p1_o = SISAL_CAST(int32_t, v_LoopA_14025_n__6_MERGE_B));
      int32_t v_BODY_14026_n__0_p2_o = 0;
      (v_BODY_14026_n__0_p2_o = SISAL_CAST(int32_t, v_LoopA_14025_n__7_MERGE_I));
      (v_BODY_14026_n__0_N = SISAL_CAST(int32_t, v_LoopA_14025_n__0_N));
      (v_BODY_14026_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopA_14025_n__8_MERGE_OLD_A));
      (v_BODY_14026_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopA_14025_n__9_MERGE_OLD_B));
      (v_BODY_14026_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopA_14025_n__10_MERGE_OLD_I));
      int32_t v_BODY_14026_n__1_p0_o = 0;
      (v_BODY_14026_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_14026_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14026_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_14026_n__1_p0_o))));
      (v_BODY_14026_n__3_B = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14026_n__0_OLD_A) + SISAL_CAST(int32_t, v_BODY_14026_n__0_OLD_B))));
      bool v_BODY_14026_n__4_p0_o = 0;
      (v_BODY_14026_n__4_p0_o = SISAL_CAST(bool, false));
      (v_LoopA_14025_bodycap_n0_p5 = v_BODY_14026_n__0_OLD_B);
      (v_LoopA_14025_bodycap_n2_p0 = v_BODY_14026_n__2_I);
      (v_LoopA_14025_bodycap_n3_p0 = v_BODY_14026_n__3_B);
      (v_LoopA_14025_bodycap_n4_p0 = v_BODY_14026_n__4_p0_o);
      (v_LoopA_14025_n__5_MERGE_A = v_LoopA_14025_bodycap_n0_p5);
      (v_LoopA_14025_n__6_MERGE_B = v_LoopA_14025_bodycap_n3_p0);
      (v_LoopA_14025_n__7_MERGE_I = v_LoopA_14025_bodycap_n2_p0);
      (v_LoopA_14025_n__8_MERGE_OLD_A = v_LoopA_14025_bodycap_n0_p5);
      (v_LoopA_14025_n__9_MERGE_OLD_B = v_LoopA_14025_bodycap_n3_p0);
      (v_LoopA_14025_n__10_MERGE_OLD_I = v_LoopA_14025_bodycap_n2_p0);
      (v_LoopA_14025_n__11_MERGE_first = v_LoopA_14025_bodycap_n4_p0);
      (v_TEST_14028_n__0_A = SISAL_CAST(int32_t, v_LoopA_14025_bodycap_n0_p5));
      (v_TEST_14028_n__0_B = SISAL_CAST(int32_t, v_LoopA_14025_bodycap_n3_p0));
      (v_TEST_14028_n__0_I = SISAL_CAST(int32_t, v_LoopA_14025_bodycap_n2_p0));
      (v_TEST_14028_n__0_N = SISAL_CAST(int32_t, v_LoopA_14025_n__0_N));
      (v_TEST_14028_n__0_OLD_A = SISAL_CAST(int32_t, v_LoopA_14025_bodycap_n0_p5));
      (v_TEST_14028_n__0_OLD_B = SISAL_CAST(int32_t, v_LoopA_14025_bodycap_n3_p0));
      (v_TEST_14028_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopA_14025_bodycap_n2_p0));
      (v_TEST_14028_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_14028_n__0_I) > SISAL_CAST(int32_t, v_TEST_14028_n__0_N))));
      (v_TEST_14028_n__3_p0_o = SISAL_CAST(bool, (!SISAL_CAST(bool, v_TEST_14028_n__1_p0_o))));
    }
    int32_t v_RETURNS_14027_n__0_p0_o = 0;
    (v_RETURNS_14027_n__0_p0_o = SISAL_CAST(int32_t, v_LoopA_14025_n__8_MERGE_OLD_A));
    int32_t v_RETURNS_14027_n__1_p0_o = 0;
    (v_RETURNS_14027_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_14027_n__0_p0_o)));
    (v_g7_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_14027_n__1_p0_o));
  }
  (v_g7_n__0_p0_i = SISAL_CAST(int32_t, v_g7_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g7_n__0_p0_i);
}

extern "C" sisal_array_t func_FI_PARAM_IDENTITY(int32_t N, sisal_array_t AIN) {
  sisal_array_t v_g8_n__0_AIN = {0};
  int32_t v_g8_n__0_N = 0;
  (v_g8_n__0_N = SISAL_CAST(int32_t, N));
  (v_g8_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  sisal_array_t v_g8_n__0_p0_i = {0};
  sisal_array_t v_g8_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_13020_n__5_MERGE_A = {0};
    int32_t v_LoopB_13020_n__6_MERGE_I = 0;
    sisal_array_t v_LoopB_13020_n__7_MERGE_OLD_A = {0};
    int32_t v_LoopB_13020_n__8_MERGE_OLD_I = 0;
    bool v_LoopB_13020_n__9_MERGE_first = 0;
    sisal_array_t v_LoopB_13020_bodycap_n0_p4 = {0};
    int32_t v_LoopB_13020_bodycap_n2_p0 = 0;
    bool v_LoopB_13020_bodycap_n3_p0 = 0;
    sisal_array_t v_LoopB_13020_n__0_AIN = {0};
    (v_LoopB_13020_n__0_AIN = SISAL_CAST(sisal_array_t, v_g8_n__0_AIN));
    int32_t v_LoopB_13020_n__0_N = 0;
    (v_LoopB_13020_n__0_N = SISAL_CAST(int32_t, v_g8_n__0_N));
    sisal_array_t v_INIT_13024_n__0_A = {0};
    sisal_array_t v_INIT_13024_n__0_AIN = {0};
    int32_t v_INIT_13024_n__1_I = 0;
    int32_t v_INIT_13024_n__0_N = 0;
    sisal_array_t v_INIT_13024_n__0_OLD_A = {0};
    int32_t v_INIT_13024_n__1_OLD_I = 0;
    (v_INIT_13024_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__0_AIN));
    (v_INIT_13024_n__0_N = SISAL_CAST(int32_t, v_LoopB_13020_n__0_N));
    (v_INIT_13024_n__1_OLD_I = SISAL_CAST(int32_t, 0));
    bool v_INIT_13024_n__2_p0_o = 0;
    (v_INIT_13024_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_13020_n__5_MERGE_A = v_INIT_13024_n__0_OLD_A);
    (v_LoopB_13020_n__6_MERGE_I = v_INIT_13024_n__1_OLD_I);
    (v_LoopB_13020_n__7_MERGE_OLD_A = v_INIT_13024_n__0_OLD_A);
    (v_LoopB_13020_n__8_MERGE_OLD_I = v_INIT_13024_n__1_OLD_I);
    (v_LoopB_13020_n__9_MERGE_first = v_INIT_13024_n__2_p0_o);
    sisal_array_t v_TEST_13023_n__0_A = {0};
    sisal_array_t v_TEST_13023_n__0_AIN = {0};
    int32_t v_TEST_13023_n__0_I = 0;
    int32_t v_TEST_13023_n__0_N = 0;
    sisal_array_t v_TEST_13023_n__0_OLD_A = {0};
    int32_t v_TEST_13023_n__0_OLD_I = 0;
    (v_TEST_13023_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__5_MERGE_A));
    (v_TEST_13023_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__0_AIN));
    (v_TEST_13023_n__0_I = SISAL_CAST(int32_t, v_LoopB_13020_n__6_MERGE_I));
    (v_TEST_13023_n__0_N = SISAL_CAST(int32_t, v_LoopB_13020_n__0_N));
    (v_TEST_13023_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__7_MERGE_OLD_A));
    (v_TEST_13023_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_13020_n__8_MERGE_OLD_I));
    bool v_TEST_13023_n__1_p0_o = 0;
    (v_TEST_13023_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_13023_n__0_I) < SISAL_CAST(int32_t, v_TEST_13023_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_13023_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_13020 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_13023_n__1_p0_o) {
      sisal_array_t v_BODY_13021_n__0_A = {0};
      sisal_array_t v_BODY_13021_n__0_AIN = {0};
      int32_t v_BODY_13021_n__2_I = 0;
      int32_t v_BODY_13021_n__0_N = 0;
      sisal_array_t v_BODY_13021_n__0_OLD_A = {0};
      int32_t v_BODY_13021_n__0_OLD_I = 0;
      sisal_array_t v_BODY_13021_n__0_p0_o = {0};
      (v_BODY_13021_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__5_MERGE_A));
      (v_BODY_13021_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__0_AIN));
      int32_t v_BODY_13021_n__0_p2_o = 0;
      (v_BODY_13021_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_13020_n__6_MERGE_I));
      (v_BODY_13021_n__0_N = SISAL_CAST(int32_t, v_LoopB_13020_n__0_N));
      (v_BODY_13021_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__7_MERGE_OLD_A));
      (v_BODY_13021_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_13020_n__8_MERGE_OLD_I));
      int32_t v_BODY_13021_n__1_p0_o = 0;
      (v_BODY_13021_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_13021_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_13021_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_13021_n__1_p0_o))));
      bool v_BODY_13021_n__3_p0_o = 0;
      (v_BODY_13021_n__3_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_13020_bodycap_n0_p4 = v_BODY_13021_n__0_OLD_A);
      (v_LoopB_13020_bodycap_n2_p0 = v_BODY_13021_n__2_I);
      (v_LoopB_13020_bodycap_n3_p0 = v_BODY_13021_n__3_p0_o);
      (v_LoopB_13020_n__5_MERGE_A = v_LoopB_13020_bodycap_n0_p4);
      (v_LoopB_13020_n__6_MERGE_I = v_LoopB_13020_bodycap_n2_p0);
      (v_LoopB_13020_n__7_MERGE_OLD_A = v_LoopB_13020_bodycap_n0_p4);
      (v_LoopB_13020_n__8_MERGE_OLD_I = v_LoopB_13020_bodycap_n2_p0);
      (v_LoopB_13020_n__9_MERGE_first = v_LoopB_13020_bodycap_n3_p0);
      (v_TEST_13023_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__5_MERGE_A));
      (v_TEST_13023_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__0_AIN));
      (v_TEST_13023_n__0_I = SISAL_CAST(int32_t, v_LoopB_13020_n__6_MERGE_I));
      (v_TEST_13023_n__0_N = SISAL_CAST(int32_t, v_LoopB_13020_n__0_N));
      (v_TEST_13023_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__7_MERGE_OLD_A));
      (v_TEST_13023_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_13020_n__8_MERGE_OLD_I));
      (v_TEST_13023_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_13023_n__0_I) < SISAL_CAST(int32_t, v_TEST_13023_n__0_N))));
    }
    sisal_array_t v_RETURNS_13022_n__0_p0_o = {0};
    (v_RETURNS_13022_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_13020_n__7_MERGE_OLD_A));
    sisal_array_t v_RETURNS_13022_n__1_p0_o = {0};
    (v_RETURNS_13022_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_13022_n__0_p0_o)));
    (v_g8_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_13022_n__1_p0_o));
  }
  (v_g8_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g8_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g8_n__0_p0_i);
}

extern "C" sisal_array_t func_FI_PARAM_BUMP(int32_t N, sisal_array_t AIN) {
  sisal_array_t v_g9_n__0_AIN = {0};
  int32_t v_g9_n__0_N = 0;
  (v_g9_n__0_N = SISAL_CAST(int32_t, N));
  (v_g9_n__0_AIN = SISAL_CAST(sisal_array_t, AIN));
  sisal_array_t v_g9_n__0_p0_i = {0};
  sisal_array_t v_g9_n__1_p0_o = {0};
  {
    sisal_array_t v_LoopB_12011_n__5_MERGE_A = {0};
    int32_t v_LoopB_12011_n__6_MERGE_I = 0;
    sisal_array_t v_LoopB_12011_n__7_MERGE_OLD_A = {0};
    int32_t v_LoopB_12011_n__8_MERGE_OLD_I = 0;
    bool v_LoopB_12011_n__9_MERGE_first = 0;
    int32_t v_LoopB_12011_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_12011_bodycap_n3_p0 = {0};
    bool v_LoopB_12011_bodycap_n5_p0 = 0;
    sisal_array_t v_LoopB_12011_n__0_AIN = {0};
    (v_LoopB_12011_n__0_AIN = SISAL_CAST(sisal_array_t, v_g9_n__0_AIN));
    int32_t v_LoopB_12011_n__0_N = 0;
    (v_LoopB_12011_n__0_N = SISAL_CAST(int32_t, v_g9_n__0_N));
    sisal_array_t v_INIT_12019_n__0_A = {0};
    sisal_array_t v_INIT_12019_n__0_AIN = {0};
    int32_t v_INIT_12019_n__1_I = 0;
    int32_t v_INIT_12019_n__0_N = 0;
    sisal_array_t v_INIT_12019_n__0_OLD_A = {0};
    int32_t v_INIT_12019_n__1_OLD_I = 0;
    (v_INIT_12019_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__0_AIN));
    (v_INIT_12019_n__0_N = SISAL_CAST(int32_t, v_LoopB_12011_n__0_N));
    (v_INIT_12019_n__1_OLD_I = SISAL_CAST(int32_t, 0));
    bool v_INIT_12019_n__2_p0_o = 0;
    (v_INIT_12019_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_12011_n__5_MERGE_A = v_INIT_12019_n__0_OLD_A);
    (v_LoopB_12011_n__6_MERGE_I = v_INIT_12019_n__1_OLD_I);
    (v_LoopB_12011_n__7_MERGE_OLD_A = v_INIT_12019_n__0_OLD_A);
    (v_LoopB_12011_n__8_MERGE_OLD_I = v_INIT_12019_n__1_OLD_I);
    (v_LoopB_12011_n__9_MERGE_first = v_INIT_12019_n__2_p0_o);
    sisal_array_t v_TEST_12018_n__0_A = {0};
    sisal_array_t v_TEST_12018_n__0_AIN = {0};
    int32_t v_TEST_12018_n__0_I = 0;
    int32_t v_TEST_12018_n__0_N = 0;
    sisal_array_t v_TEST_12018_n__0_OLD_A = {0};
    int32_t v_TEST_12018_n__0_OLD_I = 0;
    (v_TEST_12018_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__5_MERGE_A));
    (v_TEST_12018_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__0_AIN));
    (v_TEST_12018_n__0_I = SISAL_CAST(int32_t, v_LoopB_12011_n__6_MERGE_I));
    (v_TEST_12018_n__0_N = SISAL_CAST(int32_t, v_LoopB_12011_n__0_N));
    (v_TEST_12018_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__7_MERGE_OLD_A));
    (v_TEST_12018_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_12011_n__8_MERGE_OLD_I));
    bool v_TEST_12018_n__1_p0_o = 0;
    (v_TEST_12018_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_12018_n__0_I) < SISAL_CAST(int32_t, v_TEST_12018_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_12018_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_12011 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_12018_n__1_p0_o) {
      sisal_array_t v_BODY_12012_n__3_A = {0};
      sisal_array_t v_BODY_12012_n__0_AIN = {0};
      int32_t v_BODY_12012_n__2_I = 0;
      int32_t v_BODY_12012_n__0_N = 0;
      sisal_array_t v_BODY_12012_n__0_OLD_A = {0};
      int32_t v_BODY_12012_n__0_OLD_I = 0;
      sisal_array_t v_BODY_12012_n__0_p0_o = {0};
      (v_BODY_12012_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__5_MERGE_A));
      (v_BODY_12012_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__0_AIN));
      int32_t v_BODY_12012_n__0_p2_o = 0;
      (v_BODY_12012_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_12011_n__6_MERGE_I));
      (v_BODY_12012_n__0_N = SISAL_CAST(int32_t, v_LoopB_12011_n__0_N));
      (v_BODY_12012_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__7_MERGE_OLD_A));
      (v_BODY_12012_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_12011_n__8_MERGE_OLD_I));
      int32_t v_BODY_12012_n__1_p0_o = 0;
      (v_BODY_12012_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_12012_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12012_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_12012_n__1_p0_o))));
      {
        sisal_array_t v_FORALL_12013_n__0_A = v_BODY_12012_n__0_p0_o;
        sisal_array_t v_FORALL_12013_n__0_AIN = v_BODY_12012_n__0_AIN;
        int32_t v_FORALL_12013_n__0_I = v_BODY_12012_n__2_I;
        int32_t v_FORALL_12013_n__2_J;
        int32_t v_FORALL_12013_n__0_N = v_BODY_12012_n__0_N;
        sisal_array_t v_FORALL_12013_n__0_OLD_A = v_BODY_12012_n__0_OLD_A;
        int32_t v_FORALL_12013_n__0_OLD_I = v_BODY_12012_n__0_OLD_I;
        int32_t v_FORALL_12013_n__3___forall_body_0;
        int32_t v_FORALL_12013_n__2___forall_lb_2_0;
        int32_t v_FORALL_12013_n__2___forall_ub_2_0;
        sisal_array_t v_GENERATOR_12015_n__0_A;
        sisal_array_t v_GENERATOR_12015_n__0_AIN;
        int32_t v_GENERATOR_12015_n__0_I;
        int32_t v_GENERATOR_12015_n__2_J;
        int32_t v_GENERATOR_12015_n__0_N;
        sisal_array_t v_GENERATOR_12015_n__0_OLD_A;
        int32_t v_GENERATOR_12015_n__0_OLD_I;
        int32_t v_GENERATOR_12015_n__2___forall_lb_2_0;
        int32_t v_GENERATOR_12015_n__2___forall_ub_2_0;
        sisal_array_t v_BODY_12016_n__0_A;
        sisal_array_t v_BODY_12016_n__0_AIN;
        int32_t v_BODY_12016_n__0_I;
        int32_t v_BODY_12016_n__0_J;
        int32_t v_BODY_12016_n__0_N;
        sisal_array_t v_BODY_12016_n__0_OLD_A;
        int32_t v_BODY_12016_n__0_OLD_I;
        int32_t v_BODY_12016_n__0___forall_lb_2_0;
        int32_t v_BODY_12016_n__0___forall_ub_2_0;
        (v_GENERATOR_12015_n__0_N = v_FORALL_12013_n__0_N);
        (v_BODY_12012_n__3_A = sisal_array_alloc_empty(1, 6, ((uint64_t)(1 * ((v_GENERATOR_12015_n__0_N - 1) + 1)))));
        (v_BODY_12012_n__3_A.dims[0] = ((v_GENERATOR_12015_n__0_N - 1) + 1));
        (v_BODY_12012_n__3_A.lower_bound[0] = 1);
        int32_t __g_12013 = 0;
        (v_GENERATOR_12015_n__2___forall_lb_2_0 = 1);
        (v_GENERATOR_12015_n__2___forall_ub_2_0 = v_GENERATOR_12015_n__0_N);
        for ((v_GENERATOR_12015_n__2_J = 1); (v_GENERATOR_12015_n__2_J <= v_GENERATOR_12015_n__0_N); (v_GENERATOR_12015_n__2_J++)) {
          (v_BODY_12016_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_12013_n__0_A));
          (v_BODY_12016_n__0_AIN = SISAL_CAST(sisal_array_t, v_FORALL_12013_n__0_AIN));
          (v_BODY_12016_n__0_I = SISAL_CAST(int32_t, v_FORALL_12013_n__0_I));
          (v_BODY_12016_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_12015_n__2_J));
          (v_BODY_12016_n__0_N = SISAL_CAST(int32_t, v_FORALL_12013_n__0_N));
          (v_BODY_12016_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_FORALL_12013_n__0_OLD_A));
          (v_BODY_12016_n__0_OLD_I = SISAL_CAST(int32_t, v_FORALL_12013_n__0_OLD_I));
          (v_BODY_12016_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_12015_n__2___forall_lb_2_0));
          (v_BODY_12016_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_12015_n__2___forall_ub_2_0));
          int32_t v_BODY_12016_n__1_p0_o = 0;
          (v_BODY_12016_n__1_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_BODY_12016_n__0_OLD_A).data)[(SISAL_CAST(int32_t, v_BODY_12016_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_12016_n__0_OLD_A).lower_bound[0])]));
          int32_t v_BODY_12016_n__2_p0_o = 0;
          (v_BODY_12016_n__2_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_BODY_12016_n__3_p0_o = 0;
          (v_BODY_12016_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12016_n__1_p0_o) + SISAL_CAST(int32_t, v_BODY_12016_n__2_p0_o))));
          (((int32_t *)v_BODY_12012_n__3_A.data)[__g_12013] = SISAL_CAST(int32_t, v_BODY_12016_n__3_p0_o));
          (__g_12013++);
        }
      }
      bool v_BODY_12012_n__5_p0_o = 0;
      (v_BODY_12012_n__5_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_12011_bodycap_n2_p0 = v_BODY_12012_n__2_I);
      (v_LoopB_12011_bodycap_n3_p0 = v_BODY_12012_n__3_A);
      (v_LoopB_12011_bodycap_n5_p0 = v_BODY_12012_n__5_p0_o);
      (v_LoopB_12011_n__5_MERGE_A = v_LoopB_12011_bodycap_n3_p0);
      (v_LoopB_12011_n__6_MERGE_I = v_LoopB_12011_bodycap_n2_p0);
      (v_LoopB_12011_n__7_MERGE_OLD_A = v_LoopB_12011_bodycap_n3_p0);
      (v_LoopB_12011_n__8_MERGE_OLD_I = v_LoopB_12011_bodycap_n2_p0);
      (v_LoopB_12011_n__9_MERGE_first = v_LoopB_12011_bodycap_n5_p0);
      (v_TEST_12018_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__5_MERGE_A));
      (v_TEST_12018_n__0_AIN = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__0_AIN));
      (v_TEST_12018_n__0_I = SISAL_CAST(int32_t, v_LoopB_12011_n__6_MERGE_I));
      (v_TEST_12018_n__0_N = SISAL_CAST(int32_t, v_LoopB_12011_n__0_N));
      (v_TEST_12018_n__0_OLD_A = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__7_MERGE_OLD_A));
      (v_TEST_12018_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_12011_n__8_MERGE_OLD_I));
      (v_TEST_12018_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_12018_n__0_I) < SISAL_CAST(int32_t, v_TEST_12018_n__0_N))));
    }
    sisal_array_t v_RETURNS_12017_n__0_p0_o = {0};
    (v_RETURNS_12017_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_12011_n__7_MERGE_OLD_A));
    sisal_array_t v_RETURNS_12017_n__1_p0_o = {0};
    (v_RETURNS_12017_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_12017_n__0_p0_o)));
    (v_g9_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_12017_n__1_p0_o));
  }
  (v_g9_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g9_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g9_n__0_p0_i);
}

extern "C" sisal_array_t func_FI_GATHER_ZERO(int32_t N) {
  int32_t v_g10_n__0_N = 0;
  (v_g10_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g10_n__0_p0_i = {0};
  sisal_array_t v_g10_n__1_p0_o = {0};
  {
    int32_t v_LoopB_11006_n__5_MERGE_I = 0;
    int32_t v_LoopB_11006_n__6_MERGE_OLD_I = 0;
    bool v_LoopB_11006_n__7_MERGE_first = 0;
    int32_t v_LoopB_11006_bodycap_n2_p0 = 0;
    bool v_LoopB_11006_bodycap_n3_p0 = 0;
    int32_t v_LoopB_11006_n__0_N = 0;
    (v_LoopB_11006_n__0_N = SISAL_CAST(int32_t, v_g10_n__0_N));
    int32_t v_INIT_11010_n__1_I = 0;
    int32_t v_INIT_11010_n__0_N = 0;
    int32_t v_INIT_11010_n__1_OLD_I = 0;
    (v_INIT_11010_n__0_N = SISAL_CAST(int32_t, v_LoopB_11006_n__0_N));
    (v_INIT_11010_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    bool v_INIT_11010_n__2_p0_o = 0;
    (v_INIT_11010_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_11006_n__5_MERGE_I = v_INIT_11010_n__1_OLD_I);
    (v_LoopB_11006_n__6_MERGE_OLD_I = v_INIT_11010_n__1_OLD_I);
    (v_LoopB_11006_n__7_MERGE_first = v_INIT_11010_n__2_p0_o);
    int32_t v_TEST_11009_n__0_I = 0;
    int32_t v_TEST_11009_n__0_N = 0;
    int32_t v_TEST_11009_n__0_OLD_I = 0;
    (v_TEST_11009_n__0_I = SISAL_CAST(int32_t, v_LoopB_11006_n__5_MERGE_I));
    (v_TEST_11009_n__0_N = SISAL_CAST(int32_t, v_LoopB_11006_n__0_N));
    (v_TEST_11009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11006_n__6_MERGE_OLD_I));
    bool v_TEST_11009_n__1_p0_o = 0;
    (v_TEST_11009_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_11009_n__0_I) <= SISAL_CAST(int32_t, v_TEST_11009_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_11009_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_11006 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    int32_t __gseed_11006_0 = v_TEST_11009_n__0_I;
    int32_t __gbound_11006_0 = v_TEST_11009_n__0_N;
    if (((((__gbound_11006_0 - __gseed_11006_0) + 1) + 1) < 1)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' gather in LoopB_11006: sequence size < 1 (loop guard excludes even the initializer)\n");
      exit(1);
    }
    int32_t __gctr_11006_0 = 0;
    (v_g10_n__1_p0_o = sisal_array_alloc_empty(1, 6, ((uint64_t)(((__gbound_11006_0 - __gseed_11006_0) + 1) + 1))));
    (((int32_t *)v_g10_n__1_p0_o.data)[((int64_t)(__gctr_11006_0++))] = SISAL_CAST(int32_t, v_LoopB_11006_n__6_MERGE_OLD_I));
    while (v_TEST_11009_n__1_p0_o) {
      int32_t v_BODY_11007_n__2_I = 0;
      int32_t v_BODY_11007_n__0_N = 0;
      int32_t v_BODY_11007_n__0_OLD_I = 0;
      int32_t v_BODY_11007_n__0_p0_o = 0;
      (v_BODY_11007_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_11006_n__5_MERGE_I));
      (v_BODY_11007_n__0_N = SISAL_CAST(int32_t, v_LoopB_11006_n__0_N));
      (v_BODY_11007_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11006_n__6_MERGE_OLD_I));
      int32_t v_BODY_11007_n__1_p0_o = 0;
      (v_BODY_11007_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_11007_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11007_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_11007_n__1_p0_o))));
      bool v_BODY_11007_n__3_p0_o = 0;
      (v_BODY_11007_n__3_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_11006_bodycap_n2_p0 = v_BODY_11007_n__2_I);
      (v_LoopB_11006_bodycap_n3_p0 = v_BODY_11007_n__3_p0_o);
      (v_LoopB_11006_n__5_MERGE_I = v_LoopB_11006_bodycap_n2_p0);
      (v_LoopB_11006_n__6_MERGE_OLD_I = v_LoopB_11006_bodycap_n2_p0);
      (v_LoopB_11006_n__7_MERGE_first = v_LoopB_11006_bodycap_n3_p0);
      (((int32_t *)v_g10_n__1_p0_o.data)[((int64_t)(__gctr_11006_0++))] = SISAL_CAST(int32_t, v_LoopB_11006_n__6_MERGE_OLD_I));
      (v_TEST_11009_n__0_I = SISAL_CAST(int32_t, v_LoopB_11006_n__5_MERGE_I));
      (v_TEST_11009_n__0_N = SISAL_CAST(int32_t, v_LoopB_11006_n__0_N));
      (v_TEST_11009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11006_n__6_MERGE_OLD_I));
      (v_TEST_11009_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_11009_n__0_I) <= SISAL_CAST(int32_t, v_TEST_11009_n__0_N))));
    }
    int32_t v_RETURNS_11008_n__0_p0_o = 0;
    (v_RETURNS_11008_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_11006_n__6_MERGE_OLD_I));
    int32_t v_RETURNS_11008_n__3_p0_o = 0;
    (v_RETURNS_11008_n__3_p0_o = SISAL_CAST(int32_t, 1));
    int32_t v_RETURNS_11008_n__2_p0_o = 0;
    (v_RETURNS_11008_n__2_p0_o = SISAL_CAST(int32_t, sisal_dv_dimension(SISAL_CAST(int32_t, v_RETURNS_11008_n__3_p0_o), SISAL_CAST(sisal_array_t, v_RETURNS_11008_n__0_p0_o))));
    sisal_array_t v_RETURNS_11008_n__1_p0_o = {0};
    (v_RETURNS_11008_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_11008_n__0_p0_o)));
    (v_g10_n__1_p0_o = SISAL_CAST(sisal_array_t, v_g10_n__1_p0_o));
  }
  (v_g10_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g10_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g10_n__0_p0_i);
}

extern "C" sisal_array_t func_FI_GATHER_BODY_TEMP(int32_t N) {
  int32_t v_g11_n__0_N = 0;
  (v_g11_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g11_n__0_p0_i = {0};
  sisal_array_t v_g11_n__1_p0_o = {0};
  {
    int32_t v_LoopB_10001_n__5_MERGE_I = 0;
    int32_t v_LoopB_10001_n__6_MERGE_K = 0;
    int32_t v_LoopB_10001_n__7_MERGE_OLD_I = 0;
    int32_t v_LoopB_10001_n__8_MERGE_OLD_K = 0;
    bool v_LoopB_10001_n__9_MERGE_first = 0;
    int32_t v_LoopB_10001_bodycap_n2_p0 = 0;
    bool v_LoopB_10001_bodycap_n3_p0 = 0;
    int32_t v_LoopB_10001_n__0_N = 0;
    (v_LoopB_10001_n__0_N = SISAL_CAST(int32_t, v_g11_n__0_N));
    int32_t v_INIT_10005_n__1_I = 0;
    int32_t v_INIT_10005_n__2_K = 0;
    int32_t v_INIT_10005_n__0_N = 0;
    int32_t v_INIT_10005_n__1_OLD_I = 0;
    int32_t v_INIT_10005_n__2_OLD_K = 0;
    (v_INIT_10005_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_INIT_10005_n__1_OLD_I = SISAL_CAST(int32_t, 1));
    (v_INIT_10005_n__2_OLD_K = SISAL_CAST(int32_t, 0));
    bool v_INIT_10005_n__3_p0_o = 0;
    (v_INIT_10005_n__3_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_10001_n__5_MERGE_I = v_INIT_10005_n__1_OLD_I);
    (v_LoopB_10001_n__6_MERGE_K = v_INIT_10005_n__2_OLD_K);
    (v_LoopB_10001_n__7_MERGE_OLD_I = v_INIT_10005_n__1_OLD_I);
    (v_LoopB_10001_n__8_MERGE_OLD_K = v_INIT_10005_n__2_OLD_K);
    (v_LoopB_10001_n__9_MERGE_first = v_INIT_10005_n__3_p0_o);
    int32_t v_TEST_10004_n__0_I = 0;
    int32_t v_TEST_10004_n__0_K = 0;
    int32_t v_TEST_10004_n__0_N = 0;
    int32_t v_TEST_10004_n__0_OLD_I = 0;
    int32_t v_TEST_10004_n__0_OLD_K = 0;
    (v_TEST_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__5_MERGE_I));
    (v_TEST_10004_n__0_K = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_K));
    (v_TEST_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
    (v_TEST_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_OLD_I));
    (v_TEST_10004_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_K));
    bool v_TEST_10004_n__1_p0_o = 0;
    (v_TEST_10004_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10004_n__0_I) <= SISAL_CAST(int32_t, v_TEST_10004_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_10004_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_10001 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    int32_t __gseed_10001_0 = v_TEST_10004_n__0_I;
    int32_t __gbound_10001_0 = v_TEST_10004_n__0_N;
    if (((((__gbound_10001_0 - __gseed_10001_0) + 1) + 1) < 1)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' gather in LoopB_10001: sequence size < 1 (loop guard excludes even the initializer)\n");
      exit(1);
    }
    int32_t __gctr_10001_0 = 0;
    (v_g11_n__1_p0_o = sisal_array_alloc_empty(1, 6, ((uint64_t)(((__gbound_10001_0 - __gseed_10001_0) + 1) + 1))));
    (((int32_t *)v_g11_n__1_p0_o.data)[((int64_t)(__gctr_10001_0++))] = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_K));
    while (v_TEST_10004_n__1_p0_o) {
      int32_t v_BODY_10002_n__2_I = 0;
      int32_t v_BODY_10002_n__2_K = 0;
      int32_t v_BODY_10002_n__0_N = 0;
      int32_t v_BODY_10002_n__0_OLD_I = 0;
      int32_t v_BODY_10002_n__0_OLD_K = 0;
      int32_t v_BODY_10002_n__0_p0_o = 0;
      (v_BODY_10002_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_10001_n__5_MERGE_I));
      int32_t v_BODY_10002_n__0_p1_o = 0;
      (v_BODY_10002_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_K));
      (v_BODY_10002_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_BODY_10002_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_OLD_I));
      (v_BODY_10002_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_K));
      int32_t v_BODY_10002_n__1_p0_o = 0;
      (v_BODY_10002_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_10002_n__2_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10002_n__0_OLD_I) + SISAL_CAST(int32_t, v_BODY_10002_n__1_p0_o))));
      bool v_BODY_10002_n__3_p0_o = 0;
      (v_BODY_10002_n__3_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_10001_bodycap_n2_p0 = v_BODY_10002_n__2_K);
      (v_LoopB_10001_bodycap_n3_p0 = v_BODY_10002_n__3_p0_o);
      (v_LoopB_10001_n__5_MERGE_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__6_MERGE_K = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__7_MERGE_OLD_I = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__8_MERGE_OLD_K = v_LoopB_10001_bodycap_n2_p0);
      (v_LoopB_10001_n__9_MERGE_first = v_LoopB_10001_bodycap_n3_p0);
      (((int32_t *)v_g11_n__1_p0_o.data)[((int64_t)(__gctr_10001_0++))] = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_K));
      (v_TEST_10004_n__0_I = SISAL_CAST(int32_t, v_LoopB_10001_n__5_MERGE_I));
      (v_TEST_10004_n__0_K = SISAL_CAST(int32_t, v_LoopB_10001_n__6_MERGE_K));
      (v_TEST_10004_n__0_N = SISAL_CAST(int32_t, v_LoopB_10001_n__0_N));
      (v_TEST_10004_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_10001_n__7_MERGE_OLD_I));
      (v_TEST_10004_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_K));
      (v_TEST_10004_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_10004_n__0_I) <= SISAL_CAST(int32_t, v_TEST_10004_n__0_N))));
    }
    int32_t v_RETURNS_10003_n__0_p0_o = 0;
    (v_RETURNS_10003_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_10001_n__8_MERGE_OLD_K));
    int32_t v_RETURNS_10003_n__3_p0_o = 0;
    (v_RETURNS_10003_n__3_p0_o = SISAL_CAST(int32_t, 1));
    int32_t v_RETURNS_10003_n__2_p0_o = 0;
    (v_RETURNS_10003_n__2_p0_o = SISAL_CAST(int32_t, sisal_dv_dimension(SISAL_CAST(int32_t, v_RETURNS_10003_n__3_p0_o), SISAL_CAST(sisal_array_t, v_RETURNS_10003_n__0_p0_o))));
    sisal_array_t v_RETURNS_10003_n__1_p0_o = {0};
    (v_RETURNS_10003_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_10003_n__0_p0_o)));
    (v_g11_n__1_p0_o = SISAL_CAST(sisal_array_t, v_g11_n__1_p0_o));
  }
  (v_g11_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g11_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g11_n__0_p0_i);
}
