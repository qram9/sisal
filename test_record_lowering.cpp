#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_96 {
  int32_t X;
  float Y;
};
struct struct_rec_95 {
  int32_t X;
  float Y;
};
struct struct_rec_94 {
  float Y;
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
        case 12:
            return sizeof(uint32_t);
        case 96:
            return sizeof(struct struct_rec_96);
        case 95:
            return sizeof(struct struct_rec_95);
        case 94:
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
        case 97:
        case 98:
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
        case 83:
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

extern "C" struct struct_rec_96 func_MAIN();

extern "C" struct struct_rec_96 func_MAIN() {
  struct struct_rec_96 v_g1_n__0_p0_i = 0;
  struct struct_rec_96 v_g1_n__1_p0_o = {};
  {
    struct struct_rec_96 v_LET_NON_REC_10001_n__3_ORIGIN = {};
    int32_t v_LET_NON_REC_10001_n__1_p0_o = 0;
    (v_LET_NON_REC_10001_n__1_p0_o = SISAL_CAST(int32_t, 42));
    double v_LET_NON_REC_10001_n__2_p0_o = 0;
    (v_LET_NON_REC_10001_n__2_p0_o = SISAL_CAST(double, 3.f));
    (v_LET_NON_REC_10001_n__3_ORIGIN = SISAL_CAST(struct struct_rec_96, (struct_rec_96{((int32_t)v_LET_NON_REC_10001_n__1_p0_o), ((float)v_LET_NON_REC_10001_n__2_p0_o)})));
    struct struct_rec_96 v_LET_NON_REC_10001_n__4_p0_o = {};
    {
      struct struct_rec_96 v_LET_NON_REC_10002_n__0_ORIGIN = {};
      int32_t v_LET_NON_REC_10002_n__3_XX = 0;
      (v_LET_NON_REC_10002_n__0_ORIGIN = SISAL_CAST(struct struct_rec_96, v_LET_NON_REC_10001_n__3_ORIGIN));
      int32_t v_LET_NON_REC_10002_n__1_p0_o = 0;
      (v_LET_NON_REC_10002_n__1_p0_o = SISAL_CAST(int32_t, v_LET_NON_REC_10002_n__0_ORIGIN.X));
      int32_t v_LET_NON_REC_10002_n__2_p0_o = 0;
      (v_LET_NON_REC_10002_n__2_p0_o = SISAL_CAST(int32_t, 2));
      (v_LET_NON_REC_10002_n__3_XX = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_10002_n__1_p0_o) * SISAL_CAST(int32_t, v_LET_NON_REC_10002_n__2_p0_o))));
      struct struct_rec_96 v_LET_NON_REC_10002_n__4_p0_o = {};
      {
        struct struct_rec_96 v_LET_NON_REC_10003_n__1_HOME = {};
        struct struct_rec_96 v_LET_NON_REC_10003_n__0_ORIGIN = {};
        int32_t v_LET_NON_REC_10003_n__0_XX = 0;
        (v_LET_NON_REC_10003_n__0_ORIGIN = SISAL_CAST(struct struct_rec_96, v_LET_NON_REC_10002_n__0_ORIGIN));
        (v_LET_NON_REC_10003_n__0_XX = SISAL_CAST(int32_t, v_LET_NON_REC_10002_n__3_XX));
        (v_LET_NON_REC_10003_n__1_HOME = SISAL_CAST(struct struct_rec_96, (struct_rec_96{((int32_t)v_LET_NON_REC_10003_n__0_XX), v_LET_NON_REC_10003_n__0_ORIGIN.Y})));
        (v_LET_NON_REC_10002_n__4_p0_o = SISAL_CAST(struct struct_rec_96, v_LET_NON_REC_10003_n__1_HOME));
      }
      (v_LET_NON_REC_10001_n__4_p0_o = SISAL_CAST(struct struct_rec_96, v_LET_NON_REC_10002_n__4_p0_o));
    }
    (v_g1_n__1_p0_o = SISAL_CAST(struct struct_rec_96, v_LET_NON_REC_10001_n__4_p0_o));
  }
  (v_g1_n__0_p0_i = SISAL_CAST(struct struct_rec_96, v_g1_n__1_p0_o));
  return SISAL_CAST(struct struct_rec_96, v_g1_n__0_p0_i);
}
