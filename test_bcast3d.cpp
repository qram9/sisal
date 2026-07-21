#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_101 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_100 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_99 {
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
        case 99:
            return sizeof(struct struct_rec_99);
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
        case 101:
        case 102:
            return sizeof(struct struct_rec_101);
        case 100:
            return sizeof(struct struct_rec_100);
        case 95:
        case 96:
        case 97:
        case 98:
        case 104:
        case 105:
            return sizeof(sisal_array_t);
        case 7:
        case 13:
            return sizeof(int64_t);
        case 2:
        case 6:
        case 10:
        case 103:
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

extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B);

extern "C" sisal_array_t func_MAIN(sisal_array_t A, sisal_array_t B) {
  sisal_array_t v_g1_n__0_A = {0};
  sisal_array_t v_g1_n__0_B = {0};
  sisal_array_t v_g1_n__0___LFA = {0};
  sisal_array_t v_g1_n__0___LFB = {0};
  int32_t v_g1_n__4___LFMR = 0;
  int32_t v_g1_n__1___LFR1 = 0;
  int32_t v_g1_n__2___LFR2 = 0;
  sisal_array_t v_g1_n__6___LFSH = {0};
  sisal_array_t v_g1_n__6___LFSH_INT = {0};
  int32_t v_g1_n__9___LFTOTAL = 0;
  (v_g1_n__0___LFA = SISAL_CAST(sisal_array_t, A));
  (v_g1_n__0___LFB = SISAL_CAST(sisal_array_t, B));
  (v_g1_n__0_A = SISAL_CAST(sisal_array_t, v_g1_n__0___LFA));
  (v_g1_n__0_B = SISAL_CAST(sisal_array_t, v_g1_n__0___LFB));
  (v_g1_n__6___LFSH = SISAL_CAST(sisal_array_t, v_g1_n__6___LFSH_INT));
  sisal_array_t v_g1_n__0_p0_i = {0};
  (v_g1_n__1___LFR1 = SISAL_CAST(int32_t, SISAL_CAST(sisal_array_t, v_g1_n__0___LFA).rank));
  (v_g1_n__2___LFR2 = SISAL_CAST(int32_t, SISAL_CAST(sisal_array_t, v_g1_n__0___LFB).rank));
  int32_t v_g1_n__3_p0_o = 0;
  int32_t v_IF_INTEGRAL___10001_n__0___LFR1 = 0;
  (v_IF_INTEGRAL___10001_n__0___LFR1 = SISAL_CAST(int32_t, v_g1_n__1___LFR1));
  int32_t v_IF_INTEGRAL___10001_n__0___LFR2 = 0;
  (v_IF_INTEGRAL___10001_n__0___LFR2 = SISAL_CAST(int32_t, v_g1_n__2___LFR2));
  {
    int32_t v_PREDICATE_10002_n__0___LFR1 = 0;
    int32_t v_PREDICATE_10002_n__0___LFR2 = 0;
    (v_PREDICATE_10002_n__0___LFR1 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10001_n__0___LFR1));
    (v_PREDICATE_10002_n__0___LFR2 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10001_n__0___LFR2));
    bool v_PREDICATE_10002_n__1_p0_o = 0;
    (v_PREDICATE_10002_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10002_n__0___LFR1) > SISAL_CAST(int32_t, v_PREDICATE_10002_n__0___LFR2))));
    if (v_PREDICATE_10002_n__1_p0_o) {
      int32_t v_THEN_10004_n__0___LFR1 = 0;
      (v_THEN_10004_n__0___LFR1 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10001_n__0___LFR1));
      (v_g1_n__3_p0_o = SISAL_CAST(int32_t, v_THEN_10004_n__0___LFR1));
    }
    else {
      int32_t v_ELSE_10003_n__0___LFR2 = 0;
      (v_ELSE_10003_n__0___LFR2 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10001_n__0___LFR2));
      (v_g1_n__3_p0_o = SISAL_CAST(int32_t, v_ELSE_10003_n__0___LFR2));
    }
  }
  sisal_array_t v_g1_n__5_p0_o = {0};
  bool v_g1_n__5_p1_o = 0;
  {
    sisal_array_t v_FORALL_10005_n__0_A = v_g1_n__0___LFA;
    sisal_array_t v_FORALL_10005_n__0_B = v_g1_n__0___LFB;
    sisal_array_t v_FORALL_10005_n__0___LFA = v_g1_n__0___LFA;
    sisal_array_t v_FORALL_10005_n__0___LFB = v_g1_n__0___LFB;
    int32_t v_FORALL_10005_n__2___LFI;
    int32_t v_FORALL_10005_n__0___LFMR = v_g1_n__3_p0_o;
    int32_t v_FORALL_10005_n__0___LFR1 = v_g1_n__1___LFR1;
    int32_t v_FORALL_10005_n__0___LFR2 = v_g1_n__2___LFR2;
    int32_t v_FORALL_10005_n__3___forall_body_0;
    bool v_FORALL_10005_n__3___forall_body_1;
    int32_t v_FORALL_10005_n__2___forall_lb_2_0;
    int32_t v_FORALL_10005_n__2___forall_ub_2_0;
    sisal_array_t v_GENERATOR_10007_n__0_A;
    sisal_array_t v_GENERATOR_10007_n__0_B;
    sisal_array_t v_GENERATOR_10007_n__0___LFA;
    sisal_array_t v_GENERATOR_10007_n__0___LFB;
    int32_t v_GENERATOR_10007_n__2___LFI;
    int32_t v_GENERATOR_10007_n__0___LFMR;
    int32_t v_GENERATOR_10007_n__0___LFR1;
    int32_t v_GENERATOR_10007_n__0___LFR2;
    int32_t v_GENERATOR_10007_n__2___forall_lb_2_0;
    int32_t v_GENERATOR_10007_n__2___forall_ub_2_0;
    sisal_array_t v_BODY_10008_n__0_A;
    sisal_array_t v_BODY_10008_n__0_B;
    sisal_array_t v_BODY_10008_n__0___LFA;
    sisal_array_t v_BODY_10008_n__0___LFB;
    bool v_BODY_10008_n__19___LFCOMPAT;
    int32_t v_BODY_10008_n__9___LFD1;
    int32_t v_BODY_10008_n__11___LFD2;
    int32_t v_BODY_10008_n__20___LFDRES;
    int32_t v_BODY_10008_n__0___LFI;
    int32_t v_BODY_10008_n__4___LFIDX1;
    int32_t v_BODY_10008_n__8___LFIDX2;
    int32_t v_BODY_10008_n__0___LFMR;
    int32_t v_BODY_10008_n__0___LFR1;
    int32_t v_BODY_10008_n__0___LFR2;
    int32_t v_BODY_10008_n__0___forall_lb_2_0;
    int32_t v_BODY_10008_n__0___forall_ub_2_0;
    sisal_array_t v_IF_INTEGRAL___10009_n__0___LFA;
    int32_t v_IF_INTEGRAL___10009_n__0___LFIDX1;
    int32_t v_PREDICATE_10010_n__0___LFIDX1;
    sisal_array_t v_THEN_10012_n__0___LFA;
    int32_t v_THEN_10012_n__0___LFIDX1;
    sisal_array_t v_IF_INTEGRAL___10013_n__0___LFB;
    int32_t v_IF_INTEGRAL___10013_n__0___LFIDX2;
    int32_t v_PREDICATE_10014_n__0___LFIDX2;
    sisal_array_t v_THEN_10016_n__0___LFB;
    int32_t v_THEN_10016_n__0___LFIDX2;
    int32_t v_IF_INTEGRAL___10017_n__0___LFD1;
    int32_t v_IF_INTEGRAL___10017_n__0___LFD2;
    int32_t v_PREDICATE_10018_n__0___LFD1;
    int32_t v_PREDICATE_10018_n__0___LFD2;
    int32_t v_ELSE_10019_n__0___LFD2;
    int32_t v_THEN_10020_n__0___LFD1;
    (v_GENERATOR_10007_n__0___LFMR = v_FORALL_10005_n__0___LFMR);
    (v_g1_n__5_p0_o = sisal_array_alloc_empty(1, 6, ((uint64_t)(1 * ((v_GENERATOR_10007_n__0___LFMR - 1) + 1)))));
    (v_g1_n__5_p0_o.dims[0] = ((v_GENERATOR_10007_n__0___LFMR - 1) + 1));
    (v_g1_n__5_p0_o.lower_bound[0] = 1);
    (v_g1_n__5_p1_o = 0x7fffffff);
    int32_t __g_10005 = 0;
    (v_GENERATOR_10007_n__2___forall_lb_2_0 = 1);
    (v_GENERATOR_10007_n__2___forall_ub_2_0 = v_GENERATOR_10007_n__0___LFMR);
    for ((v_GENERATOR_10007_n__2___LFI = 1); (v_GENERATOR_10007_n__2___LFI <= v_GENERATOR_10007_n__0___LFMR); (v_GENERATOR_10007_n__2___LFI++)) {
      (v_BODY_10008_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_10005_n__0_A));
      (v_BODY_10008_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_10005_n__0_B));
      (v_BODY_10008_n__0___LFA = SISAL_CAST(sisal_array_t, v_FORALL_10005_n__0___LFA));
      (v_BODY_10008_n__0___LFB = SISAL_CAST(sisal_array_t, v_FORALL_10005_n__0___LFB));
      (v_BODY_10008_n__0___LFI = SISAL_CAST(int32_t, v_GENERATOR_10007_n__2___LFI));
      (v_BODY_10008_n__0___LFMR = SISAL_CAST(int32_t, v_FORALL_10005_n__0___LFMR));
      (v_BODY_10008_n__0___LFR1 = SISAL_CAST(int32_t, v_FORALL_10005_n__0___LFR1));
      (v_BODY_10008_n__0___LFR2 = SISAL_CAST(int32_t, v_FORALL_10005_n__0___LFR2));
      (v_BODY_10008_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10007_n__2___forall_lb_2_0));
      (v_BODY_10008_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10007_n__2___forall_ub_2_0));
      int32_t v_BODY_10008_n__1_p0_o = 0;
      (v_BODY_10008_n__1_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_BODY_10008_n__2_p0_o = 0;
      (v_BODY_10008_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10008_n__0___LFI) - SISAL_CAST(int32_t, v_BODY_10008_n__1_p0_o))));
      int32_t v_BODY_10008_n__3_p0_o = 0;
      (v_BODY_10008_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10008_n__0___LFMR) - SISAL_CAST(int32_t, v_BODY_10008_n__0___LFR1))));
      (v_BODY_10008_n__4___LFIDX1 = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10008_n__2_p0_o) - SISAL_CAST(int32_t, v_BODY_10008_n__3_p0_o))));
      int32_t v_BODY_10008_n__5_p0_o = 0;
      (v_BODY_10008_n__5_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_BODY_10008_n__6_p0_o = 0;
      (v_BODY_10008_n__6_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10008_n__0___LFI) - SISAL_CAST(int32_t, v_BODY_10008_n__5_p0_o))));
      int32_t v_BODY_10008_n__7_p0_o = 0;
      (v_BODY_10008_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10008_n__0___LFMR) - SISAL_CAST(int32_t, v_BODY_10008_n__0___LFR2))));
      (v_BODY_10008_n__8___LFIDX2 = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_10008_n__6_p0_o) - SISAL_CAST(int32_t, v_BODY_10008_n__7_p0_o))));
      (v_IF_INTEGRAL___10009_n__0___LFIDX1 = SISAL_CAST(int32_t, v_BODY_10008_n__4___LFIDX1));
      (v_IF_INTEGRAL___10009_n__0___LFA = SISAL_CAST(sisal_array_t, v_BODY_10008_n__0___LFA));
      {
        (v_PREDICATE_10010_n__0___LFIDX1 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10009_n__0___LFIDX1));
        int32_t v_PREDICATE_10010_n__1_p0_o = 0;
        (v_PREDICATE_10010_n__1_p0_o = SISAL_CAST(int32_t, 0));
        bool v_PREDICATE_10010_n__2_p0_o = 0;
        (v_PREDICATE_10010_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10010_n__0___LFIDX1) >= SISAL_CAST(int32_t, v_PREDICATE_10010_n__1_p0_o))));
        if (v_PREDICATE_10010_n__2_p0_o) {
          (v_THEN_10012_n__0___LFA = SISAL_CAST(sisal_array_t, v_IF_INTEGRAL___10009_n__0___LFA));
          (v_THEN_10012_n__0___LFIDX1 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10009_n__0___LFIDX1));
          int32_t v_THEN_10012_n__1_p0_o = 0;
          (v_THEN_10012_n__1_p0_o = SISAL_CAST(int32_t, sisal_dv_dimension(SISAL_CAST(int32_t, v_THEN_10012_n__0___LFIDX1), SISAL_CAST(sisal_array_t, v_THEN_10012_n__0___LFA))));
          int32_t v_THEN_10012_n__2_p0_o = 0;
          (v_THEN_10012_n__2_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_THEN_10012_n__1_p0_o)));
          (v_BODY_10008_n__9___LFD1 = SISAL_CAST(int32_t, v_THEN_10012_n__2_p0_o));
        }
        else {
          int32_t v_ELSE_10011_n__1_p0_o = 0;
          (v_ELSE_10011_n__1_p0_o = SISAL_CAST(int32_t, 1));
          (v_BODY_10008_n__9___LFD1 = SISAL_CAST(int32_t, v_ELSE_10011_n__1_p0_o));
        }
      }
      (v_IF_INTEGRAL___10013_n__0___LFIDX2 = SISAL_CAST(int32_t, v_BODY_10008_n__8___LFIDX2));
      (v_IF_INTEGRAL___10013_n__0___LFB = SISAL_CAST(sisal_array_t, v_BODY_10008_n__0___LFB));
      {
        (v_PREDICATE_10014_n__0___LFIDX2 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10013_n__0___LFIDX2));
        int32_t v_PREDICATE_10014_n__1_p0_o = 0;
        (v_PREDICATE_10014_n__1_p0_o = SISAL_CAST(int32_t, 0));
        bool v_PREDICATE_10014_n__2_p0_o = 0;
        (v_PREDICATE_10014_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10014_n__0___LFIDX2) >= SISAL_CAST(int32_t, v_PREDICATE_10014_n__1_p0_o))));
        if (v_PREDICATE_10014_n__2_p0_o) {
          (v_THEN_10016_n__0___LFB = SISAL_CAST(sisal_array_t, v_IF_INTEGRAL___10013_n__0___LFB));
          (v_THEN_10016_n__0___LFIDX2 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10013_n__0___LFIDX2));
          int32_t v_THEN_10016_n__1_p0_o = 0;
          (v_THEN_10016_n__1_p0_o = SISAL_CAST(int32_t, sisal_dv_dimension(SISAL_CAST(int32_t, v_THEN_10016_n__0___LFIDX2), SISAL_CAST(sisal_array_t, v_THEN_10016_n__0___LFB))));
          int32_t v_THEN_10016_n__2_p0_o = 0;
          (v_THEN_10016_n__2_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_THEN_10016_n__1_p0_o)));
          (v_BODY_10008_n__11___LFD2 = SISAL_CAST(int32_t, v_THEN_10016_n__2_p0_o));
        }
        else {
          int32_t v_ELSE_10015_n__1_p0_o = 0;
          (v_ELSE_10015_n__1_p0_o = SISAL_CAST(int32_t, 1));
          (v_BODY_10008_n__11___LFD2 = SISAL_CAST(int32_t, v_ELSE_10015_n__1_p0_o));
        }
      }
      bool v_BODY_10008_n__13_p0_o = 0;
      (v_BODY_10008_n__13_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_10008_n__9___LFD1) == SISAL_CAST(int32_t, v_BODY_10008_n__11___LFD2))));
      int32_t v_BODY_10008_n__14_p0_o = 0;
      (v_BODY_10008_n__14_p0_o = SISAL_CAST(int32_t, 1));
      bool v_BODY_10008_n__15_p0_o = 0;
      (v_BODY_10008_n__15_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_10008_n__9___LFD1) == SISAL_CAST(int32_t, v_BODY_10008_n__14_p0_o))));
      int32_t v_BODY_10008_n__16_p0_o = 0;
      (v_BODY_10008_n__16_p0_o = SISAL_CAST(int32_t, 1));
      bool v_BODY_10008_n__17_p0_o = 0;
      (v_BODY_10008_n__17_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_BODY_10008_n__11___LFD2) == SISAL_CAST(int32_t, v_BODY_10008_n__16_p0_o))));
      bool v_BODY_10008_n__18_p0_o = 0;
      (v_BODY_10008_n__18_p0_o = SISAL_CAST(bool, (SISAL_CAST(bool, v_BODY_10008_n__15_p0_o) || SISAL_CAST(bool, v_BODY_10008_n__17_p0_o))));
      (v_BODY_10008_n__19___LFCOMPAT = SISAL_CAST(bool, (SISAL_CAST(bool, v_BODY_10008_n__13_p0_o) || SISAL_CAST(bool, v_BODY_10008_n__18_p0_o))));
      (v_IF_INTEGRAL___10017_n__0___LFD1 = SISAL_CAST(int32_t, v_BODY_10008_n__9___LFD1));
      (v_IF_INTEGRAL___10017_n__0___LFD2 = SISAL_CAST(int32_t, v_BODY_10008_n__11___LFD2));
      {
        (v_PREDICATE_10018_n__0___LFD1 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10017_n__0___LFD1));
        (v_PREDICATE_10018_n__0___LFD2 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10017_n__0___LFD2));
        bool v_PREDICATE_10018_n__1_p0_o = 0;
        (v_PREDICATE_10018_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10018_n__0___LFD1) > SISAL_CAST(int32_t, v_PREDICATE_10018_n__0___LFD2))));
        if (v_PREDICATE_10018_n__1_p0_o) {
          (v_THEN_10020_n__0___LFD1 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10017_n__0___LFD1));
          (v_BODY_10008_n__20___LFDRES = SISAL_CAST(int32_t, v_THEN_10020_n__0___LFD1));
        }
        else {
          (v_ELSE_10019_n__0___LFD2 = SISAL_CAST(int32_t, v_IF_INTEGRAL___10017_n__0___LFD2));
          (v_BODY_10008_n__20___LFDRES = SISAL_CAST(int32_t, v_ELSE_10019_n__0___LFD2));
        }
      }
      (((int32_t *)v_g1_n__5_p0_o.data)[__g_10005] = SISAL_CAST(int32_t, v_BODY_10008_n__20___LFDRES));
      if ((SISAL_CAST(bool, v_BODY_10008_n__19___LFCOMPAT) < v_g1_n__5_p1_o)) {
        (v_g1_n__5_p1_o = SISAL_CAST(bool, v_BODY_10008_n__19___LFCOMPAT));
      }
      (__g_10005++);
    }
  }
  bool v_g1_n__7_p0_o = 0;
  (v_g1_n__7_p0_o = SISAL_CAST(bool, (!SISAL_CAST(bool, v_g1_n__5_p1_o))));
  int32_t v_g1_n__8_p0_o = 0;
  (v_g1_n__8_p0_o = SISAL_CAST(int32_t, 0.f));
  (v_g1_n__9___LFTOTAL = SISAL_CAST(int32_t, sisal_array_reduce_int_product(SISAL_CAST(sisal_array_t, v_g1_n__5_p0_o))));
  sisal_array_t v_g1_n__10_p0_o = {0};
  {
    sisal_array_t v_LET_NON_REC_10021_n__0_A = {0};
    sisal_array_t v_LET_NON_REC_10021_n__0_B = {0};
    sisal_array_t v_LET_NON_REC_10021_n__0___LFA = {0};
    sisal_array_t v_LET_NON_REC_10021_n__0___LFB = {0};
    int32_t v_LET_NON_REC_10021_n__0___LFMR = 0;
    sisal_array_t v_LET_NON_REC_10021_n__2___LFR1 = {0};
    int32_t v_LET_NON_REC_10021_n__0___LFR2 = 0;
    sisal_array_t v_LET_NON_REC_10021_n__0___LFSH = {0};
    sisal_array_t v_LET_NON_REC_10021_n__0___LFSH_INT = {0};
    int32_t v_LET_NON_REC_10021_n__0___LFTOTAL = 0;
    int32_t v_LET_NON_REC_10021_n__0_p5_o = 0;
    (v_LET_NON_REC_10021_n__0_A = SISAL_CAST(sisal_array_t, v_g1_n__0___LFA));
    (v_LET_NON_REC_10021_n__0_B = SISAL_CAST(sisal_array_t, v_g1_n__0___LFB));
    (v_LET_NON_REC_10021_n__0___LFA = SISAL_CAST(sisal_array_t, v_g1_n__0___LFA));
    (v_LET_NON_REC_10021_n__0___LFB = SISAL_CAST(sisal_array_t, v_g1_n__0___LFB));
    (v_LET_NON_REC_10021_n__0___LFMR = SISAL_CAST(int32_t, v_g1_n__3_p0_o));
    (v_LET_NON_REC_10021_n__0_p5_o = SISAL_CAST(int32_t, v_g1_n__1___LFR1));
    (v_LET_NON_REC_10021_n__0___LFR2 = SISAL_CAST(int32_t, v_g1_n__2___LFR2));
    (v_LET_NON_REC_10021_n__0___LFSH = SISAL_CAST(sisal_array_t, v_g1_n__5_p0_o));
    (v_LET_NON_REC_10021_n__0___LFSH_INT = SISAL_CAST(sisal_array_t, v_g1_n__5_p0_o));
    (v_LET_NON_REC_10021_n__0___LFTOTAL = SISAL_CAST(int32_t, v_g1_n__9___LFTOTAL));
    sisal_array_t v_LET_NON_REC_10021_n__1_p0_o = {0};
    {
      sisal_array_t v_FORALL_10022_n__0_A = v_LET_NON_REC_10021_n__0_A;
      sisal_array_t v_FORALL_10022_n__0_B = v_LET_NON_REC_10021_n__0_B;
      sisal_array_t v_FORALL_10022_n__0___LFA = v_LET_NON_REC_10021_n__0___LFA;
      sisal_array_t v_FORALL_10022_n__0___LFB = v_LET_NON_REC_10021_n__0___LFB;
      int32_t v_FORALL_10022_n__2___LFI;
      int32_t v_FORALL_10022_n__0___LFMR = v_LET_NON_REC_10021_n__0___LFMR;
      int32_t v_FORALL_10022_n__0___LFR1 = v_LET_NON_REC_10021_n__0_p5_o;
      int32_t v_FORALL_10022_n__0___LFR2 = v_LET_NON_REC_10021_n__0___LFR2;
      sisal_array_t v_FORALL_10022_n__0___LFSH = v_LET_NON_REC_10021_n__0___LFSH;
      sisal_array_t v_FORALL_10022_n__0___LFSH_INT = v_LET_NON_REC_10021_n__0___LFSH_INT;
      int32_t v_FORALL_10022_n__0___LFTOTAL = v_LET_NON_REC_10021_n__0___LFTOTAL;
      double v_FORALL_10022_n__3___forall_body_0;
      int32_t v_FORALL_10022_n__2___forall_lb_4_0;
      int32_t v_FORALL_10022_n__2___forall_ub_4_0;
      sisal_array_t v_GENERATOR_10024_n__0_A;
      sisal_array_t v_GENERATOR_10024_n__0_B;
      sisal_array_t v_GENERATOR_10024_n__0___LFA;
      sisal_array_t v_GENERATOR_10024_n__0___LFB;
      int32_t v_GENERATOR_10024_n__4___LFI;
      int32_t v_GENERATOR_10024_n__0___LFMR;
      int32_t v_GENERATOR_10024_n__0___LFR1;
      int32_t v_GENERATOR_10024_n__0___LFR2;
      sisal_array_t v_GENERATOR_10024_n__0___LFSH;
      sisal_array_t v_GENERATOR_10024_n__0___LFSH_INT;
      int32_t v_GENERATOR_10024_n__0___LFTOTAL;
      int32_t v_GENERATOR_10024_n__4___forall_lb_4_0;
      int32_t v_GENERATOR_10024_n__4___forall_ub_4_0;
      sisal_array_t v_BODY_10025_n__0_A;
      sisal_array_t v_BODY_10025_n__0_B;
      sisal_array_t v_BODY_10025_n__0___LFA;
      sisal_array_t v_BODY_10025_n__0___LFB;
      int32_t v_BODY_10025_n__0___LFI;
      int32_t v_BODY_10025_n__0___LFMR;
      int32_t v_BODY_10025_n__0___LFR1;
      int32_t v_BODY_10025_n__0___LFR2;
      sisal_array_t v_BODY_10025_n__0___LFSH;
      sisal_array_t v_BODY_10025_n__0___LFSH_INT;
      int32_t v_BODY_10025_n__0___LFTOTAL;
      int32_t v_BODY_10025_n__0___forall_lb_4_0;
      int32_t v_BODY_10025_n__0___forall_ub_4_0;
      (v_GENERATOR_10024_n__0___LFTOTAL = v_FORALL_10022_n__0___LFTOTAL);
      int32_t v_GENERATOR_10024_n__3_p0_o = 0;
      (v_GENERATOR_10024_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_GENERATOR_10024_n__0___LFTOTAL) - SISAL_CAST(int32_t, 1))));
      (v_LET_NON_REC_10021_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_10024_n__3_p0_o - 0) + 1)))));
      (v_LET_NON_REC_10021_n__1_p0_o.dims[0] = ((v_GENERATOR_10024_n__3_p0_o - 0) + 1));
      (v_LET_NON_REC_10021_n__1_p0_o.lower_bound[0] = 0);
      int32_t __g_10022 = 0;
      (v_GENERATOR_10024_n__4___forall_lb_4_0 = 0);
      (v_GENERATOR_10024_n__4___forall_ub_4_0 = v_GENERATOR_10024_n__3_p0_o);
      for ((v_GENERATOR_10024_n__4___LFI = 0); (v_GENERATOR_10024_n__4___LFI <= v_GENERATOR_10024_n__3_p0_o); (v_GENERATOR_10024_n__4___LFI++)) {
        (v_BODY_10025_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_10022_n__0_A));
        (v_BODY_10025_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_10022_n__0_B));
        (v_BODY_10025_n__0___LFA = SISAL_CAST(sisal_array_t, v_FORALL_10022_n__0___LFA));
        (v_BODY_10025_n__0___LFB = SISAL_CAST(sisal_array_t, v_FORALL_10022_n__0___LFB));
        (v_BODY_10025_n__0___LFI = SISAL_CAST(int32_t, v_GENERATOR_10024_n__4___LFI));
        (v_BODY_10025_n__0___LFMR = SISAL_CAST(int32_t, v_FORALL_10022_n__0___LFMR));
        (v_BODY_10025_n__0___LFR1 = SISAL_CAST(int32_t, v_FORALL_10022_n__0___LFR1));
        (v_BODY_10025_n__0___LFR2 = SISAL_CAST(int32_t, v_FORALL_10022_n__0___LFR2));
        (v_BODY_10025_n__0___LFSH = SISAL_CAST(sisal_array_t, v_FORALL_10022_n__0___LFSH));
        (v_BODY_10025_n__0___LFSH_INT = SISAL_CAST(sisal_array_t, v_FORALL_10022_n__0___LFSH_INT));
        (v_BODY_10025_n__0___LFTOTAL = SISAL_CAST(int32_t, v_FORALL_10022_n__0___LFTOTAL));
        (v_BODY_10025_n__0___forall_lb_4_0 = SISAL_CAST(int32_t, v_GENERATOR_10024_n__4___forall_lb_4_0));
        (v_BODY_10025_n__0___forall_ub_4_0 = SISAL_CAST(int32_t, v_GENERATOR_10024_n__4___forall_ub_4_0));
        int32_t v_BODY_10025_n__1_p0_o = 0;
        (v_BODY_10025_n__1_p0_o = SISAL_CAST(int32_t, sisal_dv_offset_at(SISAL_CAST(sisal_array_t, v_BODY_10025_n__0___LFA), SISAL_CAST(int32_t, v_BODY_10025_n__0___LFI), SISAL_CAST(sisal_array_t, v_BODY_10025_n__0___LFSH))));
        double v_BODY_10025_n__2_p0_o = 0;
        (v_BODY_10025_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_10025_n__0___LFA).data)[SISAL_CAST(int32_t, v_BODY_10025_n__1_p0_o)]));
        int32_t v_BODY_10025_n__3_p0_o = 0;
        (v_BODY_10025_n__3_p0_o = SISAL_CAST(int32_t, sisal_dv_offset_at(SISAL_CAST(sisal_array_t, v_BODY_10025_n__0___LFB), SISAL_CAST(int32_t, v_BODY_10025_n__0___LFI), SISAL_CAST(sisal_array_t, v_BODY_10025_n__0___LFSH))));
        double v_BODY_10025_n__4_p0_o = 0;
        (v_BODY_10025_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_10025_n__0___LFB).data)[SISAL_CAST(int32_t, v_BODY_10025_n__3_p0_o)]));
        double v_BODY_10025_n__5_p0_o = 0;
        (v_BODY_10025_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_10025_n__2_p0_o) + SISAL_CAST(double, v_BODY_10025_n__4_p0_o))));
        (((double *)v_LET_NON_REC_10021_n__1_p0_o.data)[__g_10022] = SISAL_CAST(double, v_BODY_10025_n__5_p0_o));
        (__g_10022++);
      }
    }
    (v_g1_n__10_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_10021_n__1_p0_o));
  }
  sisal_array_t v_g1_n__12_p0_o = {0};
  (v_g1_n__12_p0_o = SISAL_CAST(sisal_array_t, sisal_array_reshape_by_shape(SISAL_CAST(sisal_array_t, v_g1_n__10_p0_o), SISAL_CAST(sisal_array_t, v_g1_n__5_p0_o))));
  (v_g1_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g1_n__12_p0_o));
  return SISAL_CAST(sisal_array_t, v_g1_n__0_p0_i);
}
