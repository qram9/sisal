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
        case 94:
        case 95:
        case 96:
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

extern "C" int32_t func_MAIN(int32_t X);

extern "C" int32_t func_MAIN(int32_t X) {
  int32_t v_g1_n__0_X = 0;
  (v_g1_n__0_X = SISAL_CAST(int32_t, X));
  int32_t v_g1_n__0_p0_i = 0;
  int32_t v_g1_n__1_p0_o = 0;
  {
    int32_t v_FORALL_10001_n__2_I;
    int32_t v_FORALL_10001_n__0_X = v_g1_n__0_X;
    int32_t v_FORALL_10001_n__3___forall_body_0;
    int32_t v_FORALL_10001_n__2___forall_lb_3_0;
    int32_t v_FORALL_10001_n__2___forall_ub_3_0;
    int32_t v_GENERATOR_10003_n__3_I;
    int32_t v_GENERATOR_10003_n__0_X;
    int32_t v_GENERATOR_10003_n__3___forall_lb_3_0;
    int32_t v_GENERATOR_10003_n__3___forall_ub_3_0;
    int32_t v_BODY_10004_n__0_I;
    int32_t v_BODY_10004_n__2_VAL;
    int32_t v_BODY_10004_n__0_X;
    int32_t v_BODY_10004_n__0___forall_lb_3_0;
    int32_t v_BODY_10004_n__0___forall_ub_3_0;
    (v_GENERATOR_10003_n__3___forall_lb_3_0 = 1);
    (v_GENERATOR_10003_n__3___forall_ub_3_0 = 10);
    int32_t __argm_10001_0 = (-0x7fffffff);
    (v_g1_n__1_p0_o = 0);
    for ((v_GENERATOR_10003_n__3_I = 1); (v_GENERATOR_10003_n__3_I <= 10); (v_GENERATOR_10003_n__3_I++)) {
      (v_BODY_10004_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_10003_n__3_I));
      (v_BODY_10004_n__0_X = SISAL_CAST(int32_t, v_FORALL_10001_n__0_X));
      (v_BODY_10004_n__0___forall_lb_3_0 = SISAL_CAST(int32_t, v_GENERATOR_10003_n__3___forall_lb_3_0));
      (v_BODY_10004_n__0___forall_ub_3_0 = SISAL_CAST(int32_t, v_GENERATOR_10003_n__3___forall_ub_3_0));
      int32_t v_BODY_10004_n__1_p0_o = 0;
      (v_BODY_10004_n__1_p0_o = SISAL_CAST(int32_t, 10));
      (v_BODY_10004_n__2_VAL = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10004_n__1_p0_o) - SISAL_CAST(int32_t, v_BODY_10004_n__0_I))));
      if ((SISAL_CAST(int32_t, v_BODY_10004_n__2_VAL) > __argm_10001_0)) {
        (__argm_10001_0 = SISAL_CAST(int32_t, v_BODY_10004_n__2_VAL));
        (v_g1_n__1_p0_o = v_GENERATOR_10003_n__3_I);
      }
    }
  }
  (v_g1_n__0_p0_i = SISAL_CAST(int32_t, v_g1_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g1_n__0_p0_i);
}
