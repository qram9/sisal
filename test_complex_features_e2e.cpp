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
        case 94:
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

extern "C" float func_MAIN(int32_t INPUT_SEL, float INPUT_VAL, int32_t INPUT_SIZE);
extern "C" float func_PROCESSUNION(struct union_un_98 UNION_INPUT);

extern "C" float func_PROCESSUNION(struct union_un_98 UNION_INPUT) {
  struct union_un_98 v_g1_n__0_UNION_INPUT = {};
  (v_g1_n__0_UNION_INPUT = SISAL_CAST(struct union_un_98, UNION_INPUT));
  float v_g1_n__0_p0_i = 0;
  float v_g1_n__1_p0_o = 0;
  switch (v_g1_n__0_UNION_INPUT.tag) {
  case union_98_D: {
    {
      sisal_array_t v_D_11017_n__0_PAYLOAD = {0};
      struct union_un_98 v_D_11017_n__0_UNION_INPUT = {};
      sisal_array_t v_D_11017_n__0_p0_i = v_g1_n__0_UNION_INPUT.val.D;
      (v_D_11017_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
      float v_D_11017_n__1_p0_o = 0;
      {
        float v_FORALL_11018_n__2_ARRAY_ELEM;
        sisal_array_t v_FORALL_11018_n__0_PAYLOAD = v_D_11017_n__0_p0_i;
        struct union_un_98 v_FORALL_11018_n__0_UNION_INPUT = v_D_11017_n__0_UNION_INPUT;
        float v_FORALL_11018_n__3___forall_body_0;
        float v_GENERATOR_11020_n__1_ARRAY_ELEM;
        sisal_array_t v_GENERATOR_11020_n__0_PAYLOAD;
        struct union_un_98 v_GENERATOR_11020_n__0_UNION_INPUT;
        float v_BODY_11021_n__0_ARRAY_ELEM;
        sisal_array_t v_BODY_11021_n__0_PAYLOAD;
        struct union_un_98 v_BODY_11021_n__0_UNION_INPUT;
        (v_GENERATOR_11020_n__0_PAYLOAD = v_FORALL_11018_n__0_PAYLOAD);
        (v_D_11017_n__1_p0_o = 0);
        for (int32_t __k_11020 = 0; (__k_11020 < ((int32_t)v_GENERATOR_11020_n__0_PAYLOAD.size)); (__k_11020++)) {
          (v_GENERATOR_11020_n__1_ARRAY_ELEM = ((float *)v_GENERATOR_11020_n__0_PAYLOAD.data)[__k_11020]);
          (v_BODY_11021_n__0_ARRAY_ELEM = SISAL_CAST(float, v_GENERATOR_11020_n__1_ARRAY_ELEM));
          (v_BODY_11021_n__0_PAYLOAD = SISAL_CAST(sisal_array_t, v_D_11017_n__0_p0_i));
          (v_BODY_11021_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
          (v_D_11017_n__1_p0_o = (v_D_11017_n__1_p0_o + SISAL_CAST(float, v_BODY_11021_n__0_ARRAY_ELEM)));
        }
      }
      (v_g1_n__1_p0_o = SISAL_CAST(float, v_D_11017_n__1_p0_o));
      break;
    }
}
  case union_98_B: {
    {
      float v_B_11016_n__0_PAYLOAD = 0;
      struct union_un_98 v_B_11016_n__0_UNION_INPUT = {};
      float v_B_11016_n__0_p0_i = v_g1_n__0_UNION_INPUT.val.B;
      (v_B_11016_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
      float v_B_11016_n__1_p0_o = 0;
      (v_B_11016_n__1_p0_o = SISAL_CAST(float, 2.f));
      float v_B_11016_n__2_p0_o = 0;
      (v_B_11016_n__2_p0_o = SISAL_CAST(float, (SISAL_CAST(float, v_B_11016_n__0_p0_i) * SISAL_CAST(float, v_B_11016_n__1_p0_o))));
      (v_g1_n__1_p0_o = SISAL_CAST(float, v_B_11016_n__2_p0_o));
      break;
    }
}
  case union_98_A: {
    {
      int32_t v_A_11010_n__0_PAYLOAD = 0;
      struct union_un_98 v_A_11010_n__0_UNION_INPUT = {};
      int32_t v_A_11010_n__0_p0_i = v_g1_n__0_UNION_INPUT.val.A;
      (v_A_11010_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
      float v_A_11010_n__1_p0_o = 0;
      {
        float v_LoopB_11011_n__5_MERGE_LOOP_ACC = 0;
        float v_LoopB_11011_n__6_MERGE_LOOP_I = 0;
        float v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC = 0;
        float v_LoopB_11011_n__8_MERGE_OLD_LOOP_I = 0;
        bool v_LoopB_11011_n__9_MERGE_first = 0;
        float v_LoopB_11011_bodycap_n2_p0 = 0;
        float v_LoopB_11011_bodycap_n3_p0 = 0;
        bool v_LoopB_11011_bodycap_n4_p0 = 0;
        int32_t v_LoopB_11011_n__0_PAYLOAD = 0;
        (v_LoopB_11011_n__0_PAYLOAD = SISAL_CAST(int32_t, v_A_11010_n__0_p0_i));
        struct union_un_98 v_LoopB_11011_n__0_UNION_INPUT = {};
        (v_LoopB_11011_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
        float v_INIT_11015_n__2_LOOP_ACC = 0;
        float v_INIT_11015_n__1_LOOP_I = 0;
        float v_INIT_11015_n__2_OLD_LOOP_ACC = 0;
        float v_INIT_11015_n__1_OLD_LOOP_I = 0;
        int32_t v_INIT_11015_n__0_PAYLOAD = 0;
        struct union_un_98 v_INIT_11015_n__0_UNION_INPUT = {};
        (v_INIT_11015_n__0_PAYLOAD = SISAL_CAST(int32_t, v_A_11010_n__0_p0_i));
        (v_INIT_11015_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
        (v_INIT_11015_n__1_OLD_LOOP_I = SISAL_CAST(float, 1.f));
        (v_INIT_11015_n__2_OLD_LOOP_ACC = SISAL_CAST(float, 0.f));
        bool v_INIT_11015_n__3_p0_o = 0;
        (v_INIT_11015_n__3_p0_o = SISAL_CAST(bool, true));
        (v_LoopB_11011_n__5_MERGE_LOOP_ACC = v_INIT_11015_n__2_OLD_LOOP_ACC);
        (v_LoopB_11011_n__6_MERGE_LOOP_I = v_INIT_11015_n__1_OLD_LOOP_I);
        (v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC = v_INIT_11015_n__2_OLD_LOOP_ACC);
        (v_LoopB_11011_n__8_MERGE_OLD_LOOP_I = v_INIT_11015_n__1_OLD_LOOP_I);
        (v_LoopB_11011_n__9_MERGE_first = v_INIT_11015_n__3_p0_o);
        float v_TEST_11014_n__0_LOOP_ACC = 0;
        float v_TEST_11014_n__0_LOOP_I = 0;
        float v_TEST_11014_n__0_OLD_LOOP_ACC = 0;
        float v_TEST_11014_n__0_OLD_LOOP_I = 0;
        int32_t v_TEST_11014_n__0_PAYLOAD = 0;
        struct union_un_98 v_TEST_11014_n__0_UNION_INPUT = {};
        (v_TEST_11014_n__0_LOOP_ACC = SISAL_CAST(float, v_LoopB_11011_n__5_MERGE_LOOP_ACC));
        (v_TEST_11014_n__0_LOOP_I = SISAL_CAST(float, v_LoopB_11011_n__6_MERGE_LOOP_I));
        (v_TEST_11014_n__0_OLD_LOOP_ACC = SISAL_CAST(float, v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC));
        (v_TEST_11014_n__0_OLD_LOOP_I = SISAL_CAST(float, v_LoopB_11011_n__8_MERGE_OLD_LOOP_I));
        (v_TEST_11014_n__0_PAYLOAD = SISAL_CAST(int32_t, v_A_11010_n__0_p0_i));
        (v_TEST_11014_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
        double v_TEST_11014_n__2_p0_o = 0;
        (v_TEST_11014_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(int32_t, v_TEST_11014_n__0_PAYLOAD)));
        double v_TEST_11014_n__3_p0_o = 0;
        (v_TEST_11014_n__3_p0_o = SISAL_CAST(double, SISAL_CAST(float, v_TEST_11014_n__0_LOOP_I)));
        bool v_TEST_11014_n__4_p0_o = 0;
        (v_TEST_11014_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_TEST_11014_n__3_p0_o) <= SISAL_CAST(double, v_TEST_11014_n__2_p0_o))));
        #ifdef SISAL_TRAP_ZERO_TRIP
        if ((!v_TEST_11014_n__4_p0_o)) {
          fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_11011 executed 0 times (guard false on entry)\n");
          exit(1);
        }
        #endif
        while (v_TEST_11014_n__4_p0_o) {
          float v_BODY_11012_n__3_LOOP_ACC = 0;
          float v_BODY_11012_n__2_LOOP_I = 0;
          float v_BODY_11012_n__0_OLD_LOOP_ACC = 0;
          float v_BODY_11012_n__0_OLD_LOOP_I = 0;
          int32_t v_BODY_11012_n__0_PAYLOAD = 0;
          struct union_un_98 v_BODY_11012_n__0_UNION_INPUT = {};
          float v_BODY_11012_n__0_p0_o = 0;
          (v_BODY_11012_n__0_p0_o = SISAL_CAST(float, v_LoopB_11011_n__5_MERGE_LOOP_ACC));
          float v_BODY_11012_n__0_p1_o = 0;
          (v_BODY_11012_n__0_p1_o = SISAL_CAST(float, v_LoopB_11011_n__6_MERGE_LOOP_I));
          (v_BODY_11012_n__0_OLD_LOOP_ACC = SISAL_CAST(float, v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC));
          (v_BODY_11012_n__0_OLD_LOOP_I = SISAL_CAST(float, v_LoopB_11011_n__8_MERGE_OLD_LOOP_I));
          (v_BODY_11012_n__0_PAYLOAD = SISAL_CAST(int32_t, v_A_11010_n__0_p0_i));
          (v_BODY_11012_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
          float v_BODY_11012_n__1_p0_o = 0;
          (v_BODY_11012_n__1_p0_o = SISAL_CAST(float, 1.f));
          (v_BODY_11012_n__2_LOOP_I = SISAL_CAST(float, (SISAL_CAST(float, v_BODY_11012_n__0_OLD_LOOP_I) + SISAL_CAST(float, v_BODY_11012_n__1_p0_o))));
          (v_BODY_11012_n__3_LOOP_ACC = SISAL_CAST(float, (SISAL_CAST(float, v_BODY_11012_n__0_OLD_LOOP_ACC) + SISAL_CAST(float, v_BODY_11012_n__0_OLD_LOOP_I))));
          bool v_BODY_11012_n__4_p0_o = 0;
          (v_BODY_11012_n__4_p0_o = SISAL_CAST(bool, false));
          (v_LoopB_11011_bodycap_n2_p0 = v_BODY_11012_n__2_LOOP_I);
          (v_LoopB_11011_bodycap_n3_p0 = v_BODY_11012_n__3_LOOP_ACC);
          (v_LoopB_11011_bodycap_n4_p0 = v_BODY_11012_n__4_p0_o);
          (v_LoopB_11011_n__5_MERGE_LOOP_ACC = v_LoopB_11011_bodycap_n3_p0);
          (v_LoopB_11011_n__6_MERGE_LOOP_I = v_LoopB_11011_bodycap_n2_p0);
          (v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC = v_LoopB_11011_bodycap_n3_p0);
          (v_LoopB_11011_n__8_MERGE_OLD_LOOP_I = v_LoopB_11011_bodycap_n2_p0);
          (v_LoopB_11011_n__9_MERGE_first = v_LoopB_11011_bodycap_n4_p0);
          (v_TEST_11014_n__0_LOOP_ACC = SISAL_CAST(float, v_LoopB_11011_n__5_MERGE_LOOP_ACC));
          (v_TEST_11014_n__0_LOOP_I = SISAL_CAST(float, v_LoopB_11011_n__6_MERGE_LOOP_I));
          (v_TEST_11014_n__0_OLD_LOOP_ACC = SISAL_CAST(float, v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC));
          (v_TEST_11014_n__0_OLD_LOOP_I = SISAL_CAST(float, v_LoopB_11011_n__8_MERGE_OLD_LOOP_I));
          (v_TEST_11014_n__0_PAYLOAD = SISAL_CAST(int32_t, v_A_11010_n__0_p0_i));
          (v_TEST_11014_n__0_UNION_INPUT = v_g1_n__0_UNION_INPUT);
          (v_TEST_11014_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(int32_t, v_TEST_11014_n__0_PAYLOAD)));
          (v_TEST_11014_n__3_p0_o = SISAL_CAST(double, SISAL_CAST(float, v_TEST_11014_n__0_LOOP_I)));
          (v_TEST_11014_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_TEST_11014_n__3_p0_o) <= SISAL_CAST(double, v_TEST_11014_n__2_p0_o))));
        }
        float v_RETURNS_11013_n__0_p0_o = 0;
        (v_RETURNS_11013_n__0_p0_o = SISAL_CAST(float, v_LoopB_11011_n__7_MERGE_OLD_LOOP_ACC));
        float v_RETURNS_11013_n__1_p0_o = 0;
        (v_RETURNS_11013_n__1_p0_o = SISAL_CAST(float, SISAL_CAST(float, v_RETURNS_11013_n__0_p0_o)));
        (v_A_11010_n__1_p0_o = SISAL_CAST(float, v_RETURNS_11013_n__1_p0_o));
      }
      (v_g1_n__1_p0_o = SISAL_CAST(float, v_A_11010_n__1_p0_o));
      break;
    }
}
}
  (v_g1_n__0_p0_i = SISAL_CAST(float, v_g1_n__1_p0_o));
  return SISAL_CAST(float, v_g1_n__0_p0_i);
}

extern "C" float func_MAIN(int32_t INPUT_SEL, float INPUT_VAL, int32_t INPUT_SIZE) {
  int32_t v_g2_n__0_INPUT_SEL = 0;
  int32_t v_g2_n__0_INPUT_SIZE = 0;
  float v_g2_n__0_INPUT_VAL = 0;
  (v_g2_n__0_INPUT_SEL = SISAL_CAST(int32_t, INPUT_SEL));
  (v_g2_n__0_INPUT_VAL = SISAL_CAST(float, INPUT_VAL));
  (v_g2_n__0_INPUT_SIZE = SISAL_CAST(int32_t, INPUT_SIZE));
  float v_g2_n__0_p0_i = 0;
  float v_g2_n__1_p0_o = 0;
  {
    int32_t v_LET_NON_REC_10001_n__0_INPUT_SEL = 0;
    int32_t v_LET_NON_REC_10001_n__0_INPUT_SIZE = 0;
    float v_LET_NON_REC_10001_n__0_INPUT_VAL = 0;
    struct union_un_98 v_LET_NON_REC_10001_n__1_U_VAL = {};
    (v_LET_NON_REC_10001_n__0_INPUT_SEL = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SEL));
    (v_LET_NON_REC_10001_n__0_INPUT_SIZE = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SIZE));
    (v_LET_NON_REC_10001_n__0_INPUT_VAL = SISAL_CAST(float, v_g2_n__0_INPUT_VAL));
    int32_t v_IF_union_MISSING_ID_0____10002_n__0_INPUT_SEL = 0;
    (v_IF_union_MISSING_ID_0____10002_n__0_INPUT_SEL = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SEL));
    int32_t v_IF_union_MISSING_ID_0____10002_n__0_INPUT_SIZE = 0;
    (v_IF_union_MISSING_ID_0____10002_n__0_INPUT_SIZE = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SIZE));
    float v_IF_union_MISSING_ID_0____10002_n__0_INPUT_VAL = 0;
    (v_IF_union_MISSING_ID_0____10002_n__0_INPUT_VAL = SISAL_CAST(float, v_g2_n__0_INPUT_VAL));
    {
      int32_t v_PREDICATE_10003_n__0_INPUT_SEL = 0;
      (v_PREDICATE_10003_n__0_INPUT_SEL = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SEL));
      int32_t v_PREDICATE_10003_n__1_p0_o = 0;
      (v_PREDICATE_10003_n__1_p0_o = SISAL_CAST(int32_t, 1));
      bool v_PREDICATE_10003_n__2_p0_o = 0;
      (v_PREDICATE_10003_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10003_n__0_INPUT_SEL) == SISAL_CAST(int32_t, v_PREDICATE_10003_n__1_p0_o))));
      if (v_PREDICATE_10003_n__2_p0_o) {
        int32_t v_THEN_10008_n__0_INPUT_SIZE = 0;
        (v_THEN_10008_n__0_INPUT_SIZE = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SIZE));
        struct union_un_98 v_THEN_10008_n__1_p0_o = {};
        (v_THEN_10008_n__1_p0_o = make_union_98_A(v_THEN_10008_n__0_INPUT_SIZE));
        (v_LET_NON_REC_10001_n__1_U_VAL = v_THEN_10008_n__1_p0_o);
      }
      else {
        int32_t v_ELSE_10004_n__0_INPUT_SEL = 0;
        (v_ELSE_10004_n__0_INPUT_SEL = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SEL));
        int32_t v_ELSE_10004_n__0_INPUT_SIZE = 0;
        (v_ELSE_10004_n__0_INPUT_SIZE = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SIZE));
        float v_ELSE_10004_n__0_INPUT_VAL = 0;
        (v_ELSE_10004_n__0_INPUT_VAL = SISAL_CAST(float, v_g2_n__0_INPUT_VAL));
        {
          int32_t v_PREDICATE_10005_n__0_INPUT_SEL = 0;
          (v_PREDICATE_10005_n__0_INPUT_SEL = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SEL));
          int32_t v_PREDICATE_10005_n__1_p0_o = 0;
          (v_PREDICATE_10005_n__1_p0_o = SISAL_CAST(int32_t, 2));
          bool v_PREDICATE_10005_n__2_p0_o = 0;
          (v_PREDICATE_10005_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_10005_n__0_INPUT_SEL) == SISAL_CAST(int32_t, v_PREDICATE_10005_n__1_p0_o))));
          if (v_PREDICATE_10005_n__2_p0_o) {
            float v_THEN_10007_n__0_INPUT_VAL = 0;
            (v_THEN_10007_n__0_INPUT_VAL = SISAL_CAST(float, v_g2_n__0_INPUT_VAL));
            struct union_un_98 v_THEN_10007_n__1_p0_o = {};
            (v_THEN_10007_n__1_p0_o = make_union_98_B(v_THEN_10007_n__0_INPUT_VAL));
            (v_LET_NON_REC_10001_n__1_U_VAL = v_THEN_10007_n__1_p0_o);
          }
          else {
            int32_t v_ELSE_10006_n__0_INPUT_SIZE = 0;
            float v_ELSE_10006_n__0_INPUT_VAL = 0;
            (v_ELSE_10006_n__0_INPUT_SIZE = SISAL_CAST(int32_t, v_g2_n__0_INPUT_SIZE));
            (v_ELSE_10006_n__0_INPUT_VAL = SISAL_CAST(float, v_g2_n__0_INPUT_VAL));
            int32_t v_ELSE_10006_n__2_p0_o = 0;
            (v_ELSE_10006_n__2_p0_o = SISAL_CAST(int32_t, 1));
            sisal_array_t v_ELSE_10006_n__1_p0_o = {0};
            (v_ELSE_10006_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_fill_f32(((int64_t)SISAL_CAST(int32_t, v_ELSE_10006_n__2_p0_o)), ((int64_t)SISAL_CAST(int32_t, v_ELSE_10006_n__0_INPUT_SIZE)), SISAL_CAST(float, v_ELSE_10006_n__0_INPUT_VAL))));
            struct union_un_98 v_ELSE_10006_n__3_p0_o = {};
            (v_ELSE_10006_n__3_p0_o = make_union_98_D(v_ELSE_10006_n__1_p0_o));
            (v_LET_NON_REC_10001_n__1_U_VAL = v_ELSE_10006_n__3_p0_o);
          }
        }
      }
    }
    float v_LET_NON_REC_10001_n__3_p0_o = 0;
    (v_LET_NON_REC_10001_n__3_p0_o = SISAL_CAST(float, func_PROCESSUNION(v_LET_NON_REC_10001_n__1_U_VAL)));
    (v_g2_n__1_p0_o = SISAL_CAST(float, v_LET_NON_REC_10001_n__3_p0_o));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(float, v_g2_n__1_p0_o));
  return SISAL_CAST(float, v_g2_n__0_p0_i);
}
