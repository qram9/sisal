#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_108 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_107 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_106 {
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
struct FUNC_MAIN_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
};
struct FUNC_LOOP17_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  sisal_array_t res_2;
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
        case 108:
        case 109:
            return sizeof(struct struct_rec_108);
        case 107:
            return sizeof(struct struct_rec_107);
        case 106:
            return sizeof(struct struct_rec_106);
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
        case 110:
        case 111:
        case 112:
        case 113:
        case 114:
        case 115:
        case 116:
        case 117:
        case 118:
        case 119:
        case 120:
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
        case 95:
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

extern "C" struct FUNC_MAIN_results func_MAIN(int32_t REP, int32_t N, sisal_array_t VLIN, sisal_array_t VLR, sisal_array_t VSP, sisal_array_t VSTP, sisal_array_t VXNEIN);
extern "C" struct FUNC_LOOP17_results func_LOOP17(int32_t N, sisal_array_t VLIN, sisal_array_t VLR, sisal_array_t VSP, sisal_array_t VSTP, sisal_array_t VXNEIN);

extern "C" struct FUNC_LOOP17_results func_LOOP17(int32_t N, sisal_array_t VLIN, sisal_array_t VLR, sisal_array_t VSP, sisal_array_t VSTP, sisal_array_t VXNEIN) {
  int32_t v_g1_n__0_N = 0;
  sisal_array_t v_g1_n__0_VLIN = {0};
  sisal_array_t v_g1_n__0_VLR = {0};
  sisal_array_t v_g1_n__0_VSP = {0};
  sisal_array_t v_g1_n__0_VSTP = {0};
  sisal_array_t v_g1_n__0_VXNEIN = {0};
  (v_g1_n__0_N = SISAL_CAST(int32_t, N));
  (v_g1_n__0_VLIN = SISAL_CAST(sisal_array_t, VLIN));
  (v_g1_n__0_VLR = SISAL_CAST(sisal_array_t, VLR));
  (v_g1_n__0_VSP = SISAL_CAST(sisal_array_t, VSP));
  (v_g1_n__0_VSTP = SISAL_CAST(sisal_array_t, VSTP));
  (v_g1_n__0_VXNEIN = SISAL_CAST(sisal_array_t, VXNEIN));
  sisal_array_t v_g1_n__0_p0_i = {0};
  sisal_array_t v_g1_n__0_p1_i = {0};
  sisal_array_t v_g1_n__0_p2_i = {0};
  int32_t v_g1_n__1_p0_o = 0;
  (v_g1_n__1_p0_o = SISAL_CAST(int32_t, 2));
  int32_t v_g1_n__2_p0_o = 0;
  (v_g1_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_g1_n__0_N) - SISAL_CAST(int32_t, v_g1_n__1_p0_o))));
  int32_t v_g1_n__3_p0_o = 0;
  (v_g1_n__3_p0_o = SISAL_CAST(int32_t, 2));
  int32_t v_g1_n__4_p0_o = 0;
  (v_g1_n__4_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_g1_n__0_N) - SISAL_CAST(int32_t, v_g1_n__3_p0_o))));
  int32_t v_g1_n__5_p0_o = 0;
  (v_g1_n__5_p0_o = SISAL_CAST(int32_t, 2));
  int32_t v_g1_n__6_p0_o = 0;
  (v_g1_n__6_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_g1_n__0_N) - SISAL_CAST(int32_t, v_g1_n__5_p0_o))));
  sisal_array_t v_g1_n__7_p0_o = {0};
  sisal_array_t v_g1_n__7_p1_o = {0};
  sisal_array_t v_g1_n__7_p2_o = {0};
  {
    double v_LoopB_11005_n__4_E6T = 0;
    double v_LoopB_11005_n__4_OLD_E6T = 0;
    double v_LoopB_11005_n__4_OLD_XNMT = 0;
    double v_LoopB_11005_n__4_XNMT = 0;
    double v_LoopB_11005_n__5_MERGE_E3 = 0;
    double v_LoopB_11005_n__6_MERGE_E6 = 0;
    int32_t v_LoopB_11005_n__7_MERGE_I = 0;
    double v_LoopB_11005_n__8_MERGE_VE3 = 0;
    double v_LoopB_11005_n__9_MERGE_VXND = 0;
    double v_LoopB_11005_n__10_MERGE_VXNE = 0;
    double v_LoopB_11005_n__11_MERGE_XNC = 0;
    double v_LoopB_11005_n__12_MERGE_XNEI = 0;
    double v_LoopB_11005_n__13_MERGE_XNM = 0;
    double v_LoopB_11005_n__14_MERGE_OLD_E3 = 0;
    double v_LoopB_11005_n__15_MERGE_OLD_E6 = 0;
    int32_t v_LoopB_11005_n__16_MERGE_OLD_I = 0;
    double v_LoopB_11005_n__17_MERGE_OLD_VE3 = 0;
    double v_LoopB_11005_n__18_MERGE_OLD_VXND = 0;
    double v_LoopB_11005_n__19_MERGE_OLD_VXNE = 0;
    double v_LoopB_11005_n__20_MERGE_OLD_XNC = 0;
    double v_LoopB_11005_n__21_MERGE_OLD_XNEI = 0;
    double v_LoopB_11005_n__22_MERGE_OLD_XNM = 0;
    bool v_LoopB_11005_n__23_MERGE_first = 0;
    double v_LoopB_11005_bodycap_n0_p6 = 0;
    int32_t v_LoopB_11005_bodycap_n2_p0 = 0;
    double v_LoopB_11005_bodycap_n6_p0 = 0;
    double v_LoopB_11005_bodycap_n11_p0 = 0;
    double v_LoopB_11005_bodycap_n12_p0 = 0;
    double v_LoopB_11005_bodycap_n13_p0 = 0;
    double v_LoopB_11005_bodycap_n13_p1 = 0;
    double v_LoopB_11005_bodycap_n13_p2 = 0;
    double v_LoopB_11005_bodycap_n13_p3 = 0;
    bool v_LoopB_11005_bodycap_n15_p0 = 0;
    int32_t v_LoopB_11005_n__0_N = 0;
    (v_LoopB_11005_n__0_N = SISAL_CAST(int32_t, v_g1_n__0_N));
    sisal_array_t v_LoopB_11005_n__0_VLIN = {0};
    (v_LoopB_11005_n__0_VLIN = SISAL_CAST(sisal_array_t, v_g1_n__0_VLIN));
    sisal_array_t v_LoopB_11005_n__0_VLR = {0};
    (v_LoopB_11005_n__0_VLR = SISAL_CAST(sisal_array_t, v_g1_n__0_VLR));
    sisal_array_t v_LoopB_11005_n__0_VSP = {0};
    (v_LoopB_11005_n__0_VSP = SISAL_CAST(sisal_array_t, v_g1_n__0_VSP));
    sisal_array_t v_LoopB_11005_n__0_VSTP = {0};
    (v_LoopB_11005_n__0_VSTP = SISAL_CAST(sisal_array_t, v_g1_n__0_VSTP));
    sisal_array_t v_LoopB_11005_n__0_VXNEIN = {0};
    (v_LoopB_11005_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_g1_n__0_VXNEIN));
    int32_t v_LoopB_11005_n__0_p6_o = 0;
    (v_LoopB_11005_n__0_p6_o = SISAL_CAST(int32_t, v_g1_n__2_p0_o));
    int32_t v_LoopB_11005_n__0_p7_o = 0;
    (v_LoopB_11005_n__0_p7_o = SISAL_CAST(int32_t, v_g1_n__4_p0_o));
    int32_t v_LoopB_11005_n__0_p8_o = 0;
    (v_LoopB_11005_n__0_p8_o = SISAL_CAST(int32_t, v_g1_n__6_p0_o));
    double v_INIT_11018_n__12_E3 = 0;
    double v_INIT_11018_n__19_E6 = 0;
    double v_INIT_11018_n__8_E6T = 0;
    int32_t v_INIT_11018_n__0_I = 0;
    int32_t v_INIT_11018_n__0_N = 0;
    double v_INIT_11018_n__12_OLD_E3 = 0;
    double v_INIT_11018_n__19_OLD_E6 = 0;
    double v_INIT_11018_n__8_OLD_E6T = 0;
    int32_t v_INIT_11018_n__0_OLD_I = 0;
    double v_INIT_11018_n__19_OLD_VE3 = 0;
    double v_INIT_11018_n__8_OLD_VXND = 0;
    double v_INIT_11018_n__19_OLD_VXNE = 0;
    double v_INIT_11018_n__17_OLD_XNC = 0;
    double v_INIT_11018_n__18_OLD_XNEI = 0;
    double v_INIT_11018_n__19_OLD_XNM = 0;
    double v_INIT_11018_n__4_OLD_XNMT = 0;
    double v_INIT_11018_n__19_VE3 = 0;
    sisal_array_t v_INIT_11018_n__0_VLIN = {0};
    sisal_array_t v_INIT_11018_n__0_VLR = {0};
    sisal_array_t v_INIT_11018_n__0_VSP = {0};
    sisal_array_t v_INIT_11018_n__0_VSTP = {0};
    double v_INIT_11018_n__8_VXND = 0;
    double v_INIT_11018_n__19_VXNE = 0;
    sisal_array_t v_INIT_11018_n__0_VXNEIN = {0};
    double v_INIT_11018_n__17_XNC = 0;
    double v_INIT_11018_n__18_XNEI = 0;
    double v_INIT_11018_n__19_XNM = 0;
    double v_INIT_11018_n__4_XNMT = 0;
    (v_INIT_11018_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
    (v_INIT_11018_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
    (v_INIT_11018_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
    (v_INIT_11018_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
    (v_INIT_11018_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
    (v_INIT_11018_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
    double v_INIT_11018_n__1_p0_o = 0;
    (v_INIT_11018_n__1_p0_o = SISAL_CAST(double, 1.));
    double v_INIT_11018_n__2_p0_o = 0;
    (v_INIT_11018_n__2_p0_o = SISAL_CAST(double, 1.));
    double v_INIT_11018_n__3_p0_o = 0;
    (v_INIT_11018_n__3_p0_o = SISAL_CAST(double, 3.));
    (v_INIT_11018_n__4_XNMT = SISAL_CAST(double, (SISAL_CAST(double, v_INIT_11018_n__2_p0_o) / SISAL_CAST(double, v_INIT_11018_n__3_p0_o))));
    double v_INIT_11018_n__5_p0_o = 0;
    (v_INIT_11018_n__5_p0_o = SISAL_CAST(double, 1.03));
    double v_INIT_11018_n__6_p0_o = 0;
    (v_INIT_11018_n__6_p0_o = SISAL_CAST(double, 1.03));
    double v_INIT_11018_n__7_p0_o = 0;
    (v_INIT_11018_n__7_p0_o = SISAL_CAST(double, 3.07));
    (v_INIT_11018_n__8_VXND = SISAL_CAST(double, (SISAL_CAST(double, v_INIT_11018_n__6_p0_o) / SISAL_CAST(double, v_INIT_11018_n__7_p0_o))));
    double v_INIT_11018_n__9_p0_o = 0;
    (v_INIT_11018_n__9_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR).data)[(SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I) - SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR).lower_bound[0])]));
    double v_INIT_11018_n__10_p0_o = 0;
    (v_INIT_11018_n__10_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_INIT_11018_n__4_XNMT) * SISAL_CAST(double, v_INIT_11018_n__9_p0_o))));
    double v_INIT_11018_n__11_p0_o = 0;
    (v_INIT_11018_n__11_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN).data)[(SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I) - SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN).lower_bound[0])]));
    (v_INIT_11018_n__12_OLD_E3 = SISAL_CAST(double, (SISAL_CAST(double, v_INIT_11018_n__10_p0_o) + SISAL_CAST(double, v_INIT_11018_n__11_p0_o))));
    double v_INIT_11018_n__13_p0_o = 0;
    (v_INIT_11018_n__13_p0_o = SISAL_CAST(double, 5.));
    double v_INIT_11018_n__14_p0_o = 0;
    (v_INIT_11018_n__14_p0_o = SISAL_CAST(double, 5.));
    double v_INIT_11018_n__15_p0_o = 0;
    (v_INIT_11018_n__15_p0_o = SISAL_CAST(double, 3.));
    double v_INIT_11018_n__16_p0_o = 0;
    (v_INIT_11018_n__16_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_INIT_11018_n__14_p0_o) / SISAL_CAST(double, v_INIT_11018_n__15_p0_o))));
    (v_INIT_11018_n__17_XNC = SISAL_CAST(double, (SISAL_CAST(double, v_INIT_11018_n__16_p0_o) * SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3))));
    (v_INIT_11018_n__18_XNEI = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN).data)[(SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I) - SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN).lower_bound[0])]));
    double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_XNMT = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
    double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_XNC = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
    double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_XNEI = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
    double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_E3 = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
    double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_E6T = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_E6T = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
    int32_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_I = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_I = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
    int32_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_N = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_N = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
    sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VLIN = {0};
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VLIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN));
    sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VLR = {0};
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VLR = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR));
    sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VSP = {0};
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VSP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSP));
    sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VSTP = {0};
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VSTP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSTP));
    double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VXND = 0;
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VXND = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
    sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VXNEIN = {0};
    (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11019_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN));
    {
      double v_PREDICATE_11020_n__0_XNC = 0;
      double v_PREDICATE_11020_n__0_XNMT = 0;
      (v_PREDICATE_11020_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
      (v_PREDICATE_11020_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
      bool v_PREDICATE_11020_n__1_p0_o = 0;
      (v_PREDICATE_11020_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_11020_n__0_XNMT) > SISAL_CAST(double, v_PREDICATE_11020_n__0_XNC))));
      if (v_PREDICATE_11020_n__1_p0_o) {
        double v_THEN_11026_n__0_E3 = 0;
        double v_THEN_11026_n__0_E6T = 0;
        int32_t v_THEN_11026_n__0_I = 0;
        int32_t v_THEN_11026_n__0_N = 0;
        sisal_array_t v_THEN_11026_n__0_VLIN = {0};
        sisal_array_t v_THEN_11026_n__0_VLR = {0};
        sisal_array_t v_THEN_11026_n__0_VSP = {0};
        sisal_array_t v_THEN_11026_n__0_VSTP = {0};
        double v_THEN_11026_n__0_VXND = 0;
        sisal_array_t v_THEN_11026_n__0_VXNEIN = {0};
        double v_THEN_11026_n__0_XNC = 0;
        double v_THEN_11026_n__0_XNEI = 0;
        double v_THEN_11026_n__0_XNMT = 0;
        (v_THEN_11026_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
        (v_THEN_11026_n__0_E6T = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
        (v_THEN_11026_n__0_I = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
        (v_THEN_11026_n__0_N = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
        (v_THEN_11026_n__0_VLIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN));
        (v_THEN_11026_n__0_VLR = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR));
        (v_THEN_11026_n__0_VSP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSP));
        (v_THEN_11026_n__0_VSTP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSTP));
        (v_THEN_11026_n__0_VXND = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
        (v_THEN_11026_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN));
        (v_THEN_11026_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
        (v_THEN_11026_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
        (v_THEN_11026_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
        double v_THEN_11026_n__1_p0_o = 0;
        double v_THEN_11026_n__1_p1_o = 0;
        double v_THEN_11026_n__1_p2_o = 0;
        double v_THEN_11026_n__1_p3_o = 0;
        {
          double v_LET_NON_REC_11027_n__0_E3 = 0;
          double v_LET_NON_REC_11027_n__4_E6 = 0;
          double v_LET_NON_REC_11027_n__0_E6T = 0;
          int32_t v_LET_NON_REC_11027_n__0_I = 0;
          int32_t v_LET_NON_REC_11027_n__0_N = 0;
          sisal_array_t v_LET_NON_REC_11027_n__0_VLIN = {0};
          sisal_array_t v_LET_NON_REC_11027_n__0_VLR = {0};
          sisal_array_t v_LET_NON_REC_11027_n__0_VSP = {0};
          sisal_array_t v_LET_NON_REC_11027_n__0_VSTP = {0};
          double v_LET_NON_REC_11027_n__0_VXND = 0;
          sisal_array_t v_LET_NON_REC_11027_n__0_VXNEIN = {0};
          double v_LET_NON_REC_11027_n__0_XNC = 0;
          double v_LET_NON_REC_11027_n__0_XNEI = 0;
          double v_LET_NON_REC_11027_n__0_XNMT = 0;
          (v_LET_NON_REC_11027_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
          (v_LET_NON_REC_11027_n__0_E6T = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
          (v_LET_NON_REC_11027_n__0_I = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
          (v_LET_NON_REC_11027_n__0_N = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
          (v_LET_NON_REC_11027_n__0_VLIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN));
          (v_LET_NON_REC_11027_n__0_VLR = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR));
          (v_LET_NON_REC_11027_n__0_VSP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSP));
          (v_LET_NON_REC_11027_n__0_VSTP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSTP));
          (v_LET_NON_REC_11027_n__0_VXND = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
          (v_LET_NON_REC_11027_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN));
          (v_LET_NON_REC_11027_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
          (v_LET_NON_REC_11027_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
          (v_LET_NON_REC_11027_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
          double v_LET_NON_REC_11027_n__1_p0_o = 0;
          (v_LET_NON_REC_11027_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11027_n__0_VSP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11027_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11027_n__0_VSP).lower_bound[0])]));
          double v_LET_NON_REC_11027_n__2_p0_o = 0;
          (v_LET_NON_REC_11027_n__2_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11027_n__0_XNMT) * SISAL_CAST(double, v_LET_NON_REC_11027_n__1_p0_o))));
          double v_LET_NON_REC_11027_n__3_p0_o = 0;
          (v_LET_NON_REC_11027_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11027_n__0_VSTP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11027_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11027_n__0_VSTP).lower_bound[0])]));
          (v_LET_NON_REC_11027_n__4_E6 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11027_n__2_p0_o) + SISAL_CAST(double, v_LET_NON_REC_11027_n__3_p0_o))));
          (v_THEN_11026_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_11027_n__4_E6));
          (v_THEN_11026_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_11027_n__4_E6));
          (v_THEN_11026_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_11027_n__4_E6));
          (v_THEN_11026_n__1_p3_o = SISAL_CAST(double, v_LET_NON_REC_11027_n__4_E6));
        }
        (v_INIT_11018_n__19_VE3 = SISAL_CAST(double, v_THEN_11026_n__1_p0_o));
        (v_INIT_11018_n__19_OLD_E6 = SISAL_CAST(double, v_THEN_11026_n__1_p1_o));
        (v_INIT_11018_n__19_VXNE = SISAL_CAST(double, v_THEN_11026_n__1_p2_o));
        (v_INIT_11018_n__19_XNM = SISAL_CAST(double, v_THEN_11026_n__1_p3_o));
      }
      else {
        double v_ELSE_11021_n__0_XNEI = 0;
        (v_ELSE_11021_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
        double v_ELSE_11021_n__0_XNC = 0;
        (v_ELSE_11021_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
        double v_ELSE_11021_n__0_E3 = 0;
        (v_ELSE_11021_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
        double v_ELSE_11021_n__0_XNMT = 0;
        (v_ELSE_11021_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
        double v_ELSE_11021_n__0_E6T = 0;
        (v_ELSE_11021_n__0_E6T = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
        int32_t v_ELSE_11021_n__0_I = 0;
        (v_ELSE_11021_n__0_I = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
        int32_t v_ELSE_11021_n__0_N = 0;
        (v_ELSE_11021_n__0_N = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
        sisal_array_t v_ELSE_11021_n__0_VLIN = {0};
        (v_ELSE_11021_n__0_VLIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN));
        sisal_array_t v_ELSE_11021_n__0_VLR = {0};
        (v_ELSE_11021_n__0_VLR = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR));
        sisal_array_t v_ELSE_11021_n__0_VSP = {0};
        (v_ELSE_11021_n__0_VSP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSP));
        sisal_array_t v_ELSE_11021_n__0_VSTP = {0};
        (v_ELSE_11021_n__0_VSTP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSTP));
        double v_ELSE_11021_n__0_VXND = 0;
        (v_ELSE_11021_n__0_VXND = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
        sisal_array_t v_ELSE_11021_n__0_VXNEIN = {0};
        (v_ELSE_11021_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN));
        {
          double v_PREDICATE_11022_n__0_XNC = 0;
          double v_PREDICATE_11022_n__0_XNEI = 0;
          (v_PREDICATE_11022_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
          (v_PREDICATE_11022_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
          bool v_PREDICATE_11022_n__1_p0_o = 0;
          (v_PREDICATE_11022_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_11022_n__0_XNEI) > SISAL_CAST(double, v_PREDICATE_11022_n__0_XNC))));
          if (v_PREDICATE_11022_n__1_p0_o) {
            double v_THEN_11024_n__0_E3 = 0;
            double v_THEN_11024_n__0_E6T = 0;
            int32_t v_THEN_11024_n__0_I = 0;
            int32_t v_THEN_11024_n__0_N = 0;
            sisal_array_t v_THEN_11024_n__0_VLIN = {0};
            sisal_array_t v_THEN_11024_n__0_VLR = {0};
            sisal_array_t v_THEN_11024_n__0_VSP = {0};
            sisal_array_t v_THEN_11024_n__0_VSTP = {0};
            double v_THEN_11024_n__0_VXND = 0;
            sisal_array_t v_THEN_11024_n__0_VXNEIN = {0};
            double v_THEN_11024_n__0_XNC = 0;
            double v_THEN_11024_n__0_XNEI = 0;
            double v_THEN_11024_n__0_XNMT = 0;
            (v_THEN_11024_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
            (v_THEN_11024_n__0_E6T = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
            (v_THEN_11024_n__0_I = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
            (v_THEN_11024_n__0_N = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
            (v_THEN_11024_n__0_VLIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN));
            (v_THEN_11024_n__0_VLR = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR));
            (v_THEN_11024_n__0_VSP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSP));
            (v_THEN_11024_n__0_VSTP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSTP));
            (v_THEN_11024_n__0_VXND = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
            (v_THEN_11024_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN));
            (v_THEN_11024_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
            (v_THEN_11024_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
            (v_THEN_11024_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
            double v_THEN_11024_n__1_p0_o = 0;
            double v_THEN_11024_n__1_p1_o = 0;
            double v_THEN_11024_n__1_p2_o = 0;
            double v_THEN_11024_n__1_p3_o = 0;
            {
              double v_LET_NON_REC_11025_n__0_E3 = 0;
              double v_LET_NON_REC_11025_n__4_E6 = 0;
              double v_LET_NON_REC_11025_n__0_E6T = 0;
              int32_t v_LET_NON_REC_11025_n__0_I = 0;
              int32_t v_LET_NON_REC_11025_n__0_N = 0;
              sisal_array_t v_LET_NON_REC_11025_n__0_VLIN = {0};
              sisal_array_t v_LET_NON_REC_11025_n__0_VLR = {0};
              sisal_array_t v_LET_NON_REC_11025_n__0_VSP = {0};
              sisal_array_t v_LET_NON_REC_11025_n__0_VSTP = {0};
              double v_LET_NON_REC_11025_n__0_VXND = 0;
              sisal_array_t v_LET_NON_REC_11025_n__0_VXNEIN = {0};
              double v_LET_NON_REC_11025_n__0_XNC = 0;
              double v_LET_NON_REC_11025_n__0_XNEI = 0;
              double v_LET_NON_REC_11025_n__0_XNMT = 0;
              (v_LET_NON_REC_11025_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
              (v_LET_NON_REC_11025_n__0_E6T = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
              (v_LET_NON_REC_11025_n__0_I = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
              (v_LET_NON_REC_11025_n__0_N = SISAL_CAST(int32_t, v_INIT_11018_n__0_OLD_I));
              (v_LET_NON_REC_11025_n__0_VLIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLIN));
              (v_LET_NON_REC_11025_n__0_VLR = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VLR));
              (v_LET_NON_REC_11025_n__0_VSP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSP));
              (v_LET_NON_REC_11025_n__0_VSTP = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VSTP));
              (v_LET_NON_REC_11025_n__0_VXND = SISAL_CAST(double, v_INIT_11018_n__8_VXND));
              (v_LET_NON_REC_11025_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_INIT_11018_n__0_VXNEIN));
              (v_LET_NON_REC_11025_n__0_XNC = SISAL_CAST(double, v_INIT_11018_n__17_XNC));
              (v_LET_NON_REC_11025_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
              (v_LET_NON_REC_11025_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
              double v_LET_NON_REC_11025_n__1_p0_o = 0;
              (v_LET_NON_REC_11025_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11025_n__0_VSP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11025_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11025_n__0_VSP).lower_bound[0])]));
              double v_LET_NON_REC_11025_n__2_p0_o = 0;
              (v_LET_NON_REC_11025_n__2_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11025_n__0_XNMT) * SISAL_CAST(double, v_LET_NON_REC_11025_n__1_p0_o))));
              double v_LET_NON_REC_11025_n__3_p0_o = 0;
              (v_LET_NON_REC_11025_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11025_n__0_VSTP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11025_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11025_n__0_VSTP).lower_bound[0])]));
              (v_LET_NON_REC_11025_n__4_E6 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11025_n__2_p0_o) + SISAL_CAST(double, v_LET_NON_REC_11025_n__3_p0_o))));
              (v_THEN_11024_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_11025_n__4_E6));
              (v_THEN_11024_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_11025_n__4_E6));
              (v_THEN_11024_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_11025_n__4_E6));
              (v_THEN_11024_n__1_p3_o = SISAL_CAST(double, v_LET_NON_REC_11025_n__4_E6));
            }
            (v_INIT_11018_n__19_VE3 = SISAL_CAST(double, v_THEN_11024_n__1_p0_o));
            (v_INIT_11018_n__19_OLD_E6 = SISAL_CAST(double, v_THEN_11024_n__1_p1_o));
            (v_INIT_11018_n__19_VXNE = SISAL_CAST(double, v_THEN_11024_n__1_p2_o));
            (v_INIT_11018_n__19_XNM = SISAL_CAST(double, v_THEN_11024_n__1_p3_o));
          }
          else {
            double v_ELSE_11023_n__0_E3 = 0;
            double v_ELSE_11023_n__0_XNEI = 0;
            double v_ELSE_11023_n__0_XNMT = 0;
            (v_ELSE_11023_n__0_E3 = SISAL_CAST(double, v_INIT_11018_n__12_OLD_E3));
            (v_ELSE_11023_n__0_XNMT = SISAL_CAST(double, v_INIT_11018_n__4_XNMT));
            (v_ELSE_11023_n__0_XNEI = SISAL_CAST(double, v_INIT_11018_n__18_XNEI));
            double v_ELSE_11023_n__1_p0_o = 0;
            (v_ELSE_11023_n__1_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11023_n__0_E3) + SISAL_CAST(double, v_ELSE_11023_n__0_E3))));
            double v_ELSE_11023_n__2_p0_o = 0;
            (v_ELSE_11023_n__2_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11023_n__1_p0_o) - SISAL_CAST(double, v_ELSE_11023_n__0_XNMT))));
            double v_ELSE_11023_n__3_p0_o = 0;
            (v_ELSE_11023_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11023_n__0_E3) + SISAL_CAST(double, v_ELSE_11023_n__0_E3))));
            double v_ELSE_11023_n__4_p0_o = 0;
            (v_ELSE_11023_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11023_n__3_p0_o) - SISAL_CAST(double, v_ELSE_11023_n__0_XNEI))));
            double v_ELSE_11023_n__5_p0_o = 0;
            (v_ELSE_11023_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11023_n__0_E3) + SISAL_CAST(double, v_ELSE_11023_n__0_E3))));
            double v_ELSE_11023_n__6_p0_o = 0;
            (v_ELSE_11023_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11023_n__5_p0_o) - SISAL_CAST(double, v_ELSE_11023_n__0_XNMT))));
            (v_INIT_11018_n__19_VE3 = SISAL_CAST(double, v_ELSE_11023_n__0_E3));
            (v_INIT_11018_n__19_OLD_E6 = SISAL_CAST(double, v_ELSE_11023_n__2_p0_o));
            (v_INIT_11018_n__19_VXNE = SISAL_CAST(double, v_ELSE_11023_n__4_p0_o));
            (v_INIT_11018_n__19_XNM = SISAL_CAST(double, v_ELSE_11023_n__6_p0_o));
          }
        }
      }
    }
    bool v_INIT_11018_n__21_p0_o = 0;
    (v_INIT_11018_n__21_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_11005_n__4_E6T = v_INIT_11018_n__8_VXND);
    (v_LoopB_11005_n__4_XNMT = v_INIT_11018_n__4_XNMT);
    (v_LoopB_11005_n__4_OLD_E6T = v_INIT_11018_n__8_VXND);
    (v_LoopB_11005_n__4_OLD_XNMT = v_INIT_11018_n__4_XNMT);
    (v_LoopB_11005_n__5_MERGE_E3 = v_INIT_11018_n__12_OLD_E3);
    (v_LoopB_11005_n__6_MERGE_E6 = v_INIT_11018_n__19_OLD_E6);
    (v_LoopB_11005_n__7_MERGE_I = v_INIT_11018_n__0_OLD_I);
    (v_LoopB_11005_n__8_MERGE_VE3 = v_INIT_11018_n__19_VE3);
    (v_LoopB_11005_n__9_MERGE_VXND = v_INIT_11018_n__8_VXND);
    (v_LoopB_11005_n__10_MERGE_VXNE = v_INIT_11018_n__19_VXNE);
    (v_LoopB_11005_n__11_MERGE_XNC = v_INIT_11018_n__17_XNC);
    (v_LoopB_11005_n__12_MERGE_XNEI = v_INIT_11018_n__18_XNEI);
    (v_LoopB_11005_n__13_MERGE_XNM = v_INIT_11018_n__19_XNM);
    (v_LoopB_11005_n__14_MERGE_OLD_E3 = v_INIT_11018_n__12_OLD_E3);
    (v_LoopB_11005_n__15_MERGE_OLD_E6 = v_INIT_11018_n__19_OLD_E6);
    (v_LoopB_11005_n__16_MERGE_OLD_I = v_INIT_11018_n__0_OLD_I);
    (v_LoopB_11005_n__17_MERGE_OLD_VE3 = v_INIT_11018_n__19_VE3);
    (v_LoopB_11005_n__18_MERGE_OLD_VXND = v_INIT_11018_n__8_VXND);
    (v_LoopB_11005_n__19_MERGE_OLD_VXNE = v_INIT_11018_n__19_VXNE);
    (v_LoopB_11005_n__20_MERGE_OLD_XNC = v_INIT_11018_n__17_XNC);
    (v_LoopB_11005_n__21_MERGE_OLD_XNEI = v_INIT_11018_n__18_XNEI);
    (v_LoopB_11005_n__22_MERGE_OLD_XNM = v_INIT_11018_n__19_XNM);
    (v_LoopB_11005_n__23_MERGE_first = v_INIT_11018_n__21_p0_o);
    double v_TEST_11017_n__0_E3 = 0;
    double v_TEST_11017_n__0_E6 = 0;
    double v_TEST_11017_n__0_E6T = 0;
    int32_t v_TEST_11017_n__0_I = 0;
    int32_t v_TEST_11017_n__0_N = 0;
    double v_TEST_11017_n__0_OLD_E3 = 0;
    double v_TEST_11017_n__0_OLD_E6 = 0;
    double v_TEST_11017_n__0_OLD_E6T = 0;
    int32_t v_TEST_11017_n__0_OLD_I = 0;
    double v_TEST_11017_n__0_OLD_VE3 = 0;
    double v_TEST_11017_n__0_OLD_VXND = 0;
    double v_TEST_11017_n__0_OLD_VXNE = 0;
    double v_TEST_11017_n__0_OLD_XNC = 0;
    double v_TEST_11017_n__0_OLD_XNEI = 0;
    double v_TEST_11017_n__0_OLD_XNM = 0;
    double v_TEST_11017_n__0_OLD_XNMT = 0;
    double v_TEST_11017_n__0_VE3 = 0;
    sisal_array_t v_TEST_11017_n__0_VLIN = {0};
    sisal_array_t v_TEST_11017_n__0_VLR = {0};
    sisal_array_t v_TEST_11017_n__0_VSP = {0};
    sisal_array_t v_TEST_11017_n__0_VSTP = {0};
    double v_TEST_11017_n__0_VXND = 0;
    double v_TEST_11017_n__0_VXNE = 0;
    sisal_array_t v_TEST_11017_n__0_VXNEIN = {0};
    double v_TEST_11017_n__0_XNC = 0;
    double v_TEST_11017_n__0_XNEI = 0;
    double v_TEST_11017_n__0_XNM = 0;
    double v_TEST_11017_n__0_XNMT = 0;
    (v_TEST_11017_n__0_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
    (v_TEST_11017_n__0_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
    (v_TEST_11017_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__4_E6T));
    (v_TEST_11017_n__0_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
    (v_TEST_11017_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
    (v_TEST_11017_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__14_MERGE_OLD_E3));
    (v_TEST_11017_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__15_MERGE_OLD_E6));
    (v_TEST_11017_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__4_OLD_E6T));
    (v_TEST_11017_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__16_MERGE_OLD_I));
    (v_TEST_11017_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__17_MERGE_OLD_VE3));
    (v_TEST_11017_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__18_MERGE_OLD_VXND));
    (v_TEST_11017_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__19_MERGE_OLD_VXNE));
    (v_TEST_11017_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__20_MERGE_OLD_XNC));
    (v_TEST_11017_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__21_MERGE_OLD_XNEI));
    (v_TEST_11017_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__22_MERGE_OLD_XNM));
    (v_TEST_11017_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__4_OLD_XNMT));
    (v_TEST_11017_n__0_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
    (v_TEST_11017_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
    (v_TEST_11017_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
    (v_TEST_11017_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
    (v_TEST_11017_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
    (v_TEST_11017_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
    (v_TEST_11017_n__0_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
    (v_TEST_11017_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
    (v_TEST_11017_n__0_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
    (v_TEST_11017_n__0_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
    (v_TEST_11017_n__0_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
    (v_TEST_11017_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__4_XNMT));
    int32_t v_TEST_11017_n__1_p0_o = 0;
    (v_TEST_11017_n__1_p0_o = SISAL_CAST(int32_t, 2));
    bool v_TEST_11017_n__2_p0_o = 0;
    (v_TEST_11017_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_11017_n__0_I) > SISAL_CAST(int32_t, v_TEST_11017_n__1_p0_o))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_11017_n__2_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_11005 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    int32_t __gctr_11005_2 = 0;
    (v_g1_n__7_p2_o = sisal_array_alloc_empty(1, 4, ((uint64_t)v_LoopB_11005_n__0_p8_o)));
    int32_t __gctr_11005_1 = 0;
    (v_g1_n__7_p1_o = sisal_array_alloc_empty(1, 4, ((uint64_t)v_LoopB_11005_n__0_p7_o)));
    int32_t __gctr_11005_0 = 0;
    (v_g1_n__7_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)v_LoopB_11005_n__0_p6_o)));
    while (v_TEST_11017_n__2_p0_o) {
      double v_BODY_11006_n__6_E3 = 0;
      double v_BODY_11006_n__13_E6 = 0;
      double v_BODY_11006_n__0_E6T = 0;
      int32_t v_BODY_11006_n__2_I = 0;
      int32_t v_BODY_11006_n__0_N = 0;
      double v_BODY_11006_n__0_OLD_E3 = 0;
      double v_BODY_11006_n__0_OLD_E6 = 0;
      double v_BODY_11006_n__0_OLD_E6T = 0;
      int32_t v_BODY_11006_n__0_OLD_I = 0;
      double v_BODY_11006_n__0_OLD_VE3 = 0;
      double v_BODY_11006_n__0_OLD_VXND = 0;
      double v_BODY_11006_n__0_OLD_VXNE = 0;
      double v_BODY_11006_n__0_OLD_XNC = 0;
      double v_BODY_11006_n__0_OLD_XNEI = 0;
      double v_BODY_11006_n__0_OLD_XNM = 0;
      double v_BODY_11006_n__0_OLD_XNMT = 0;
      double v_BODY_11006_n__13_VE3 = 0;
      sisal_array_t v_BODY_11006_n__0_VLIN = {0};
      sisal_array_t v_BODY_11006_n__0_VLR = {0};
      sisal_array_t v_BODY_11006_n__0_VSP = {0};
      sisal_array_t v_BODY_11006_n__0_VSTP = {0};
      double v_BODY_11006_n__0_VXND = 0;
      double v_BODY_11006_n__13_VXNE = 0;
      sisal_array_t v_BODY_11006_n__0_VXNEIN = {0};
      double v_BODY_11006_n__11_XNC = 0;
      double v_BODY_11006_n__12_XNEI = 0;
      double v_BODY_11006_n__13_XNM = 0;
      double v_BODY_11006_n__0_XNMT = 0;
      double v_BODY_11006_n__0_p1_o = 0;
      double v_BODY_11006_n__0_p16_o = 0;
      double v_BODY_11006_n__0_p22_o = 0;
      double v_BODY_11006_n__0_p26_o = 0;
      double v_BODY_11006_n__0_p0_o = 0;
      (v_BODY_11006_n__0_p0_o = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
      (v_BODY_11006_n__0_p1_o = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
      (v_BODY_11006_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__4_E6T));
      int32_t v_BODY_11006_n__0_p3_o = 0;
      (v_BODY_11006_n__0_p3_o = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
      (v_BODY_11006_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
      (v_BODY_11006_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__14_MERGE_OLD_E3));
      (v_BODY_11006_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__15_MERGE_OLD_E6));
      (v_BODY_11006_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__4_OLD_E6T));
      (v_BODY_11006_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__16_MERGE_OLD_I));
      (v_BODY_11006_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__17_MERGE_OLD_VE3));
      (v_BODY_11006_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__18_MERGE_OLD_VXND));
      (v_BODY_11006_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__19_MERGE_OLD_VXNE));
      (v_BODY_11006_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__20_MERGE_OLD_XNC));
      (v_BODY_11006_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__21_MERGE_OLD_XNEI));
      (v_BODY_11006_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__22_MERGE_OLD_XNM));
      (v_BODY_11006_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__4_OLD_XNMT));
      (v_BODY_11006_n__0_p16_o = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
      (v_BODY_11006_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
      (v_BODY_11006_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
      (v_BODY_11006_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
      (v_BODY_11006_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
      double v_BODY_11006_n__0_p21_o = 0;
      (v_BODY_11006_n__0_p21_o = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
      (v_BODY_11006_n__0_p22_o = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
      (v_BODY_11006_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
      double v_BODY_11006_n__0_p24_o = 0;
      (v_BODY_11006_n__0_p24_o = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
      double v_BODY_11006_n__0_p25_o = 0;
      (v_BODY_11006_n__0_p25_o = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
      (v_BODY_11006_n__0_p26_o = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
      (v_BODY_11006_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__4_XNMT));
      int32_t v_BODY_11006_n__1_p0_o = 0;
      (v_BODY_11006_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_11006_n__2_I = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_11006_n__0_OLD_I) - SISAL_CAST(int32_t, v_BODY_11006_n__1_p0_o))));
      double v_BODY_11006_n__3_p0_o = 0;
      (v_BODY_11006_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11006_n__0_VLR).data)[(SISAL_CAST(int32_t, v_BODY_11006_n__2_I) - SISAL_CAST(sisal_array_t, v_BODY_11006_n__0_VLR).lower_bound[0])]));
      double v_BODY_11006_n__4_p0_o = 0;
      (v_BODY_11006_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11006_n__0_OLD_XNM) * SISAL_CAST(double, v_BODY_11006_n__3_p0_o))));
      double v_BODY_11006_n__5_p0_o = 0;
      (v_BODY_11006_n__5_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11006_n__0_VLIN).data)[(SISAL_CAST(int32_t, v_BODY_11006_n__2_I) - SISAL_CAST(sisal_array_t, v_BODY_11006_n__0_VLIN).lower_bound[0])]));
      (v_BODY_11006_n__6_E3 = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11006_n__4_p0_o) + SISAL_CAST(double, v_BODY_11006_n__5_p0_o))));
      double v_BODY_11006_n__7_p0_o = 0;
      (v_BODY_11006_n__7_p0_o = SISAL_CAST(double, 5.));
      double v_BODY_11006_n__8_p0_o = 0;
      (v_BODY_11006_n__8_p0_o = SISAL_CAST(double, 5.));
      double v_BODY_11006_n__9_p0_o = 0;
      (v_BODY_11006_n__9_p0_o = SISAL_CAST(double, 3.));
      double v_BODY_11006_n__10_p0_o = 0;
      (v_BODY_11006_n__10_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11006_n__8_p0_o) / SISAL_CAST(double, v_BODY_11006_n__9_p0_o))));
      (v_BODY_11006_n__11_XNC = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11006_n__10_p0_o) * SISAL_CAST(double, v_BODY_11006_n__6_E3))));
      (v_BODY_11006_n__12_XNEI = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11006_n__0_VXNEIN).data)[(SISAL_CAST(int32_t, v_BODY_11006_n__2_I) - SISAL_CAST(sisal_array_t, v_BODY_11006_n__0_VXNEIN).lower_bound[0])]));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNM = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNC = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNEI = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_E3 = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_E6 = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_E6 = SISAL_CAST(double, v_BODY_11006_n__13_E6));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_E6T = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
      int32_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_I = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_I = SISAL_CAST(int32_t, v_BODY_11006_n__2_I));
      int32_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_N = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_E3 = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_E6 = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_E6T = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
      int32_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_I = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_VE3 = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_VXND = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_VXNE = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNC = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNEI = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNMT = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VE3 = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VE3 = SISAL_CAST(double, v_BODY_11006_n__13_VE3));
      sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VLIN = {0};
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
      sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VLR = {0};
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
      sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VSP = {0};
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
      sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VSTP = {0};
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VXND = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VXNE = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VXNE = SISAL_CAST(double, v_BODY_11006_n__13_VXNE));
      sisal_array_t v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VXNEIN = {0};
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNM = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNM = SISAL_CAST(double, v_BODY_11006_n__13_XNM));
      double v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNMT = 0;
      (v_IF_DOUBLE__DOUBLE__DOUBLE__DOUBLE___11007_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
      {
        double v_PREDICATE_11008_n__0_OLD_XNM = 0;
        double v_PREDICATE_11008_n__0_XNC = 0;
        (v_PREDICATE_11008_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
        (v_PREDICATE_11008_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
        bool v_PREDICATE_11008_n__1_p0_o = 0;
        (v_PREDICATE_11008_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_11008_n__0_OLD_XNM) > SISAL_CAST(double, v_PREDICATE_11008_n__0_XNC))));
        if (v_PREDICATE_11008_n__1_p0_o) {
          double v_THEN_11014_n__0_E3 = 0;
          double v_THEN_11014_n__0_E6 = 0;
          double v_THEN_11014_n__0_E6T = 0;
          int32_t v_THEN_11014_n__0_I = 0;
          int32_t v_THEN_11014_n__0_N = 0;
          double v_THEN_11014_n__0_OLD_E3 = 0;
          double v_THEN_11014_n__0_OLD_E6 = 0;
          double v_THEN_11014_n__0_OLD_E6T = 0;
          int32_t v_THEN_11014_n__0_OLD_I = 0;
          double v_THEN_11014_n__0_OLD_VE3 = 0;
          double v_THEN_11014_n__0_OLD_VXND = 0;
          double v_THEN_11014_n__0_OLD_VXNE = 0;
          double v_THEN_11014_n__0_OLD_XNC = 0;
          double v_THEN_11014_n__0_OLD_XNEI = 0;
          double v_THEN_11014_n__0_OLD_XNM = 0;
          double v_THEN_11014_n__0_OLD_XNMT = 0;
          double v_THEN_11014_n__0_VE3 = 0;
          sisal_array_t v_THEN_11014_n__0_VLIN = {0};
          sisal_array_t v_THEN_11014_n__0_VLR = {0};
          sisal_array_t v_THEN_11014_n__0_VSP = {0};
          sisal_array_t v_THEN_11014_n__0_VSTP = {0};
          double v_THEN_11014_n__0_VXND = 0;
          double v_THEN_11014_n__0_VXNE = 0;
          sisal_array_t v_THEN_11014_n__0_VXNEIN = {0};
          double v_THEN_11014_n__0_XNC = 0;
          double v_THEN_11014_n__0_XNEI = 0;
          double v_THEN_11014_n__0_XNM = 0;
          double v_THEN_11014_n__0_XNMT = 0;
          (v_THEN_11014_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
          (v_THEN_11014_n__0_E6 = SISAL_CAST(double, v_BODY_11006_n__13_E6));
          (v_THEN_11014_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
          (v_THEN_11014_n__0_I = SISAL_CAST(int32_t, v_BODY_11006_n__2_I));
          (v_THEN_11014_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
          (v_THEN_11014_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
          (v_THEN_11014_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
          (v_THEN_11014_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
          (v_THEN_11014_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
          (v_THEN_11014_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
          (v_THEN_11014_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
          (v_THEN_11014_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
          (v_THEN_11014_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
          (v_THEN_11014_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
          (v_THEN_11014_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
          (v_THEN_11014_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
          (v_THEN_11014_n__0_VE3 = SISAL_CAST(double, v_BODY_11006_n__13_VE3));
          (v_THEN_11014_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
          (v_THEN_11014_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
          (v_THEN_11014_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
          (v_THEN_11014_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
          (v_THEN_11014_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
          (v_THEN_11014_n__0_VXNE = SISAL_CAST(double, v_BODY_11006_n__13_VXNE));
          (v_THEN_11014_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
          (v_THEN_11014_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
          (v_THEN_11014_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
          (v_THEN_11014_n__0_XNM = SISAL_CAST(double, v_BODY_11006_n__13_XNM));
          (v_THEN_11014_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
          double v_THEN_11014_n__1_p0_o = 0;
          double v_THEN_11014_n__1_p1_o = 0;
          double v_THEN_11014_n__1_p2_o = 0;
          double v_THEN_11014_n__1_p3_o = 0;
          {
            double v_LET_NON_REC_11015_n__0_E3 = 0;
            double v_LET_NON_REC_11015_n__4_E6 = 0;
            double v_LET_NON_REC_11015_n__0_E6T = 0;
            int32_t v_LET_NON_REC_11015_n__0_I = 0;
            int32_t v_LET_NON_REC_11015_n__0_N = 0;
            double v_LET_NON_REC_11015_n__0_OLD_E3 = 0;
            double v_LET_NON_REC_11015_n__0_OLD_E6 = 0;
            double v_LET_NON_REC_11015_n__0_OLD_E6T = 0;
            int32_t v_LET_NON_REC_11015_n__0_OLD_I = 0;
            double v_LET_NON_REC_11015_n__0_OLD_VE3 = 0;
            double v_LET_NON_REC_11015_n__0_OLD_VXND = 0;
            double v_LET_NON_REC_11015_n__0_OLD_VXNE = 0;
            double v_LET_NON_REC_11015_n__0_OLD_XNC = 0;
            double v_LET_NON_REC_11015_n__0_OLD_XNEI = 0;
            double v_LET_NON_REC_11015_n__0_OLD_XNM = 0;
            double v_LET_NON_REC_11015_n__0_OLD_XNMT = 0;
            double v_LET_NON_REC_11015_n__0_VE3 = 0;
            sisal_array_t v_LET_NON_REC_11015_n__0_VLIN = {0};
            sisal_array_t v_LET_NON_REC_11015_n__0_VLR = {0};
            sisal_array_t v_LET_NON_REC_11015_n__0_VSP = {0};
            sisal_array_t v_LET_NON_REC_11015_n__0_VSTP = {0};
            double v_LET_NON_REC_11015_n__0_VXND = 0;
            double v_LET_NON_REC_11015_n__0_VXNE = 0;
            sisal_array_t v_LET_NON_REC_11015_n__0_VXNEIN = {0};
            double v_LET_NON_REC_11015_n__0_XNC = 0;
            double v_LET_NON_REC_11015_n__0_XNEI = 0;
            double v_LET_NON_REC_11015_n__0_XNM = 0;
            double v_LET_NON_REC_11015_n__0_XNMT = 0;
            (v_LET_NON_REC_11015_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
            double v_LET_NON_REC_11015_n__0_p1_o = 0;
            (v_LET_NON_REC_11015_n__0_p1_o = SISAL_CAST(double, v_BODY_11006_n__13_E6));
            (v_LET_NON_REC_11015_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
            (v_LET_NON_REC_11015_n__0_I = SISAL_CAST(int32_t, v_BODY_11006_n__2_I));
            (v_LET_NON_REC_11015_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
            (v_LET_NON_REC_11015_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
            (v_LET_NON_REC_11015_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
            (v_LET_NON_REC_11015_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
            (v_LET_NON_REC_11015_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
            (v_LET_NON_REC_11015_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
            (v_LET_NON_REC_11015_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
            (v_LET_NON_REC_11015_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
            (v_LET_NON_REC_11015_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
            (v_LET_NON_REC_11015_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
            (v_LET_NON_REC_11015_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
            (v_LET_NON_REC_11015_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
            (v_LET_NON_REC_11015_n__0_VE3 = SISAL_CAST(double, v_BODY_11006_n__13_VE3));
            (v_LET_NON_REC_11015_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
            (v_LET_NON_REC_11015_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
            (v_LET_NON_REC_11015_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
            (v_LET_NON_REC_11015_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
            (v_LET_NON_REC_11015_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
            (v_LET_NON_REC_11015_n__0_VXNE = SISAL_CAST(double, v_BODY_11006_n__13_VXNE));
            (v_LET_NON_REC_11015_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
            (v_LET_NON_REC_11015_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
            (v_LET_NON_REC_11015_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
            (v_LET_NON_REC_11015_n__0_XNM = SISAL_CAST(double, v_BODY_11006_n__13_XNM));
            (v_LET_NON_REC_11015_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
            double v_LET_NON_REC_11015_n__1_p0_o = 0;
            (v_LET_NON_REC_11015_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11015_n__0_VSP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11015_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11015_n__0_VSP).lower_bound[0])]));
            double v_LET_NON_REC_11015_n__2_p0_o = 0;
            (v_LET_NON_REC_11015_n__2_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11015_n__0_OLD_XNM) * SISAL_CAST(double, v_LET_NON_REC_11015_n__1_p0_o))));
            double v_LET_NON_REC_11015_n__3_p0_o = 0;
            (v_LET_NON_REC_11015_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11015_n__0_VSTP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11015_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11015_n__0_VSTP).lower_bound[0])]));
            (v_LET_NON_REC_11015_n__4_E6 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11015_n__2_p0_o) + SISAL_CAST(double, v_LET_NON_REC_11015_n__3_p0_o))));
            (v_THEN_11014_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_11015_n__4_E6));
            (v_THEN_11014_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_11015_n__4_E6));
            (v_THEN_11014_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_11015_n__4_E6));
            (v_THEN_11014_n__1_p3_o = SISAL_CAST(double, v_LET_NON_REC_11015_n__4_E6));
          }
          (v_BODY_11006_n__13_VE3 = SISAL_CAST(double, v_THEN_11014_n__1_p0_o));
          (v_BODY_11006_n__13_E6 = SISAL_CAST(double, v_THEN_11014_n__1_p1_o));
          (v_BODY_11006_n__13_VXNE = SISAL_CAST(double, v_THEN_11014_n__1_p2_o));
          (v_BODY_11006_n__13_XNM = SISAL_CAST(double, v_THEN_11014_n__1_p3_o));
        }
        else {
          double v_ELSE_11009_n__0_XNEI = 0;
          (v_ELSE_11009_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
          double v_ELSE_11009_n__0_XNC = 0;
          (v_ELSE_11009_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
          double v_ELSE_11009_n__0_E3 = 0;
          (v_ELSE_11009_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
          double v_ELSE_11009_n__0_OLD_XNM = 0;
          (v_ELSE_11009_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
          double v_ELSE_11009_n__0_E6 = 0;
          (v_ELSE_11009_n__0_E6 = SISAL_CAST(double, v_BODY_11006_n__13_E6));
          double v_ELSE_11009_n__0_E6T = 0;
          (v_ELSE_11009_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
          int32_t v_ELSE_11009_n__0_I = 0;
          (v_ELSE_11009_n__0_I = SISAL_CAST(int32_t, v_BODY_11006_n__2_I));
          int32_t v_ELSE_11009_n__0_N = 0;
          (v_ELSE_11009_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
          double v_ELSE_11009_n__0_OLD_E3 = 0;
          (v_ELSE_11009_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
          double v_ELSE_11009_n__0_OLD_E6 = 0;
          (v_ELSE_11009_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
          double v_ELSE_11009_n__0_OLD_E6T = 0;
          (v_ELSE_11009_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
          int32_t v_ELSE_11009_n__0_OLD_I = 0;
          (v_ELSE_11009_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
          double v_ELSE_11009_n__0_OLD_VE3 = 0;
          (v_ELSE_11009_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
          double v_ELSE_11009_n__0_OLD_VXND = 0;
          (v_ELSE_11009_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
          double v_ELSE_11009_n__0_OLD_VXNE = 0;
          (v_ELSE_11009_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
          double v_ELSE_11009_n__0_OLD_XNC = 0;
          (v_ELSE_11009_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
          double v_ELSE_11009_n__0_OLD_XNEI = 0;
          (v_ELSE_11009_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
          double v_ELSE_11009_n__0_OLD_XNMT = 0;
          (v_ELSE_11009_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
          double v_ELSE_11009_n__0_VE3 = 0;
          (v_ELSE_11009_n__0_VE3 = SISAL_CAST(double, v_BODY_11006_n__13_VE3));
          sisal_array_t v_ELSE_11009_n__0_VLIN = {0};
          (v_ELSE_11009_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
          sisal_array_t v_ELSE_11009_n__0_VLR = {0};
          (v_ELSE_11009_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
          sisal_array_t v_ELSE_11009_n__0_VSP = {0};
          (v_ELSE_11009_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
          sisal_array_t v_ELSE_11009_n__0_VSTP = {0};
          (v_ELSE_11009_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
          double v_ELSE_11009_n__0_VXND = 0;
          (v_ELSE_11009_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
          double v_ELSE_11009_n__0_VXNE = 0;
          (v_ELSE_11009_n__0_VXNE = SISAL_CAST(double, v_BODY_11006_n__13_VXNE));
          sisal_array_t v_ELSE_11009_n__0_VXNEIN = {0};
          (v_ELSE_11009_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
          double v_ELSE_11009_n__0_XNM = 0;
          (v_ELSE_11009_n__0_XNM = SISAL_CAST(double, v_BODY_11006_n__13_XNM));
          double v_ELSE_11009_n__0_XNMT = 0;
          (v_ELSE_11009_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
          {
            double v_PREDICATE_11010_n__0_XNC = 0;
            double v_PREDICATE_11010_n__0_XNEI = 0;
            (v_PREDICATE_11010_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
            (v_PREDICATE_11010_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
            bool v_PREDICATE_11010_n__1_p0_o = 0;
            (v_PREDICATE_11010_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_11010_n__0_XNEI) > SISAL_CAST(double, v_PREDICATE_11010_n__0_XNC))));
            if (v_PREDICATE_11010_n__1_p0_o) {
              double v_THEN_11012_n__0_E3 = 0;
              double v_THEN_11012_n__0_E6 = 0;
              double v_THEN_11012_n__0_E6T = 0;
              int32_t v_THEN_11012_n__0_I = 0;
              int32_t v_THEN_11012_n__0_N = 0;
              double v_THEN_11012_n__0_OLD_E3 = 0;
              double v_THEN_11012_n__0_OLD_E6 = 0;
              double v_THEN_11012_n__0_OLD_E6T = 0;
              int32_t v_THEN_11012_n__0_OLD_I = 0;
              double v_THEN_11012_n__0_OLD_VE3 = 0;
              double v_THEN_11012_n__0_OLD_VXND = 0;
              double v_THEN_11012_n__0_OLD_VXNE = 0;
              double v_THEN_11012_n__0_OLD_XNC = 0;
              double v_THEN_11012_n__0_OLD_XNEI = 0;
              double v_THEN_11012_n__0_OLD_XNM = 0;
              double v_THEN_11012_n__0_OLD_XNMT = 0;
              double v_THEN_11012_n__0_VE3 = 0;
              sisal_array_t v_THEN_11012_n__0_VLIN = {0};
              sisal_array_t v_THEN_11012_n__0_VLR = {0};
              sisal_array_t v_THEN_11012_n__0_VSP = {0};
              sisal_array_t v_THEN_11012_n__0_VSTP = {0};
              double v_THEN_11012_n__0_VXND = 0;
              double v_THEN_11012_n__0_VXNE = 0;
              sisal_array_t v_THEN_11012_n__0_VXNEIN = {0};
              double v_THEN_11012_n__0_XNC = 0;
              double v_THEN_11012_n__0_XNEI = 0;
              double v_THEN_11012_n__0_XNM = 0;
              double v_THEN_11012_n__0_XNMT = 0;
              (v_THEN_11012_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
              (v_THEN_11012_n__0_E6 = SISAL_CAST(double, v_BODY_11006_n__13_E6));
              (v_THEN_11012_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
              (v_THEN_11012_n__0_I = SISAL_CAST(int32_t, v_BODY_11006_n__2_I));
              (v_THEN_11012_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
              (v_THEN_11012_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
              (v_THEN_11012_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
              (v_THEN_11012_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
              (v_THEN_11012_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
              (v_THEN_11012_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
              (v_THEN_11012_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
              (v_THEN_11012_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
              (v_THEN_11012_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
              (v_THEN_11012_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
              (v_THEN_11012_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
              (v_THEN_11012_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
              (v_THEN_11012_n__0_VE3 = SISAL_CAST(double, v_BODY_11006_n__13_VE3));
              (v_THEN_11012_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
              (v_THEN_11012_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
              (v_THEN_11012_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
              (v_THEN_11012_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
              (v_THEN_11012_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
              (v_THEN_11012_n__0_VXNE = SISAL_CAST(double, v_BODY_11006_n__13_VXNE));
              (v_THEN_11012_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
              (v_THEN_11012_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
              (v_THEN_11012_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
              (v_THEN_11012_n__0_XNM = SISAL_CAST(double, v_BODY_11006_n__13_XNM));
              (v_THEN_11012_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
              double v_THEN_11012_n__1_p0_o = 0;
              double v_THEN_11012_n__1_p1_o = 0;
              double v_THEN_11012_n__1_p2_o = 0;
              double v_THEN_11012_n__1_p3_o = 0;
              {
                double v_LET_NON_REC_11013_n__0_E3 = 0;
                double v_LET_NON_REC_11013_n__4_E6 = 0;
                double v_LET_NON_REC_11013_n__0_E6T = 0;
                int32_t v_LET_NON_REC_11013_n__0_I = 0;
                int32_t v_LET_NON_REC_11013_n__0_N = 0;
                double v_LET_NON_REC_11013_n__0_OLD_E3 = 0;
                double v_LET_NON_REC_11013_n__0_OLD_E6 = 0;
                double v_LET_NON_REC_11013_n__0_OLD_E6T = 0;
                int32_t v_LET_NON_REC_11013_n__0_OLD_I = 0;
                double v_LET_NON_REC_11013_n__0_OLD_VE3 = 0;
                double v_LET_NON_REC_11013_n__0_OLD_VXND = 0;
                double v_LET_NON_REC_11013_n__0_OLD_VXNE = 0;
                double v_LET_NON_REC_11013_n__0_OLD_XNC = 0;
                double v_LET_NON_REC_11013_n__0_OLD_XNEI = 0;
                double v_LET_NON_REC_11013_n__0_OLD_XNM = 0;
                double v_LET_NON_REC_11013_n__0_OLD_XNMT = 0;
                double v_LET_NON_REC_11013_n__0_VE3 = 0;
                sisal_array_t v_LET_NON_REC_11013_n__0_VLIN = {0};
                sisal_array_t v_LET_NON_REC_11013_n__0_VLR = {0};
                sisal_array_t v_LET_NON_REC_11013_n__0_VSP = {0};
                sisal_array_t v_LET_NON_REC_11013_n__0_VSTP = {0};
                double v_LET_NON_REC_11013_n__0_VXND = 0;
                double v_LET_NON_REC_11013_n__0_VXNE = 0;
                sisal_array_t v_LET_NON_REC_11013_n__0_VXNEIN = {0};
                double v_LET_NON_REC_11013_n__0_XNC = 0;
                double v_LET_NON_REC_11013_n__0_XNEI = 0;
                double v_LET_NON_REC_11013_n__0_XNM = 0;
                double v_LET_NON_REC_11013_n__0_XNMT = 0;
                (v_LET_NON_REC_11013_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
                double v_LET_NON_REC_11013_n__0_p1_o = 0;
                (v_LET_NON_REC_11013_n__0_p1_o = SISAL_CAST(double, v_BODY_11006_n__13_E6));
                (v_LET_NON_REC_11013_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
                (v_LET_NON_REC_11013_n__0_I = SISAL_CAST(int32_t, v_BODY_11006_n__2_I));
                (v_LET_NON_REC_11013_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
                (v_LET_NON_REC_11013_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
                (v_LET_NON_REC_11013_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
                (v_LET_NON_REC_11013_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
                (v_LET_NON_REC_11013_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
                (v_LET_NON_REC_11013_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
                (v_LET_NON_REC_11013_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
                (v_LET_NON_REC_11013_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
                (v_LET_NON_REC_11013_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
                (v_LET_NON_REC_11013_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
                (v_LET_NON_REC_11013_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
                (v_LET_NON_REC_11013_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
                (v_LET_NON_REC_11013_n__0_VE3 = SISAL_CAST(double, v_BODY_11006_n__13_VE3));
                (v_LET_NON_REC_11013_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
                (v_LET_NON_REC_11013_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
                (v_LET_NON_REC_11013_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
                (v_LET_NON_REC_11013_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
                (v_LET_NON_REC_11013_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
                (v_LET_NON_REC_11013_n__0_VXNE = SISAL_CAST(double, v_BODY_11006_n__13_VXNE));
                (v_LET_NON_REC_11013_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
                (v_LET_NON_REC_11013_n__0_XNC = SISAL_CAST(double, v_BODY_11006_n__11_XNC));
                (v_LET_NON_REC_11013_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
                (v_LET_NON_REC_11013_n__0_XNM = SISAL_CAST(double, v_BODY_11006_n__13_XNM));
                (v_LET_NON_REC_11013_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
                double v_LET_NON_REC_11013_n__1_p0_o = 0;
                (v_LET_NON_REC_11013_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11013_n__0_VSP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11013_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11013_n__0_VSP).lower_bound[0])]));
                double v_LET_NON_REC_11013_n__2_p0_o = 0;
                (v_LET_NON_REC_11013_n__2_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11013_n__0_OLD_XNM) * SISAL_CAST(double, v_LET_NON_REC_11013_n__1_p0_o))));
                double v_LET_NON_REC_11013_n__3_p0_o = 0;
                (v_LET_NON_REC_11013_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_11013_n__0_VSTP).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_11013_n__0_I) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_11013_n__0_VSTP).lower_bound[0])]));
                (v_LET_NON_REC_11013_n__4_E6 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_11013_n__2_p0_o) + SISAL_CAST(double, v_LET_NON_REC_11013_n__3_p0_o))));
                (v_THEN_11012_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_11013_n__4_E6));
                (v_THEN_11012_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_11013_n__4_E6));
                (v_THEN_11012_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_11013_n__4_E6));
                (v_THEN_11012_n__1_p3_o = SISAL_CAST(double, v_LET_NON_REC_11013_n__4_E6));
              }
              (v_BODY_11006_n__13_VE3 = SISAL_CAST(double, v_THEN_11012_n__1_p0_o));
              (v_BODY_11006_n__13_E6 = SISAL_CAST(double, v_THEN_11012_n__1_p1_o));
              (v_BODY_11006_n__13_VXNE = SISAL_CAST(double, v_THEN_11012_n__1_p2_o));
              (v_BODY_11006_n__13_XNM = SISAL_CAST(double, v_THEN_11012_n__1_p3_o));
            }
            else {
              double v_ELSE_11011_n__0_E3 = 0;
              double v_ELSE_11011_n__0_OLD_XNM = 0;
              double v_ELSE_11011_n__0_XNEI = 0;
              (v_ELSE_11011_n__0_E3 = SISAL_CAST(double, v_BODY_11006_n__6_E3));
              (v_ELSE_11011_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
              (v_ELSE_11011_n__0_XNEI = SISAL_CAST(double, v_BODY_11006_n__12_XNEI));
              double v_ELSE_11011_n__1_p0_o = 0;
              (v_ELSE_11011_n__1_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11011_n__0_E3) + SISAL_CAST(double, v_ELSE_11011_n__0_E3))));
              double v_ELSE_11011_n__2_p0_o = 0;
              (v_ELSE_11011_n__2_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11011_n__1_p0_o) - SISAL_CAST(double, v_ELSE_11011_n__0_OLD_XNM))));
              double v_ELSE_11011_n__3_p0_o = 0;
              (v_ELSE_11011_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11011_n__0_E3) + SISAL_CAST(double, v_ELSE_11011_n__0_E3))));
              double v_ELSE_11011_n__4_p0_o = 0;
              (v_ELSE_11011_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11011_n__3_p0_o) - SISAL_CAST(double, v_ELSE_11011_n__0_XNEI))));
              double v_ELSE_11011_n__5_p0_o = 0;
              (v_ELSE_11011_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11011_n__0_E3) + SISAL_CAST(double, v_ELSE_11011_n__0_E3))));
              double v_ELSE_11011_n__6_p0_o = 0;
              (v_ELSE_11011_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_11011_n__5_p0_o) - SISAL_CAST(double, v_ELSE_11011_n__0_OLD_XNM))));
              (v_BODY_11006_n__13_VE3 = SISAL_CAST(double, v_ELSE_11011_n__0_E3));
              (v_BODY_11006_n__13_E6 = SISAL_CAST(double, v_ELSE_11011_n__2_p0_o));
              (v_BODY_11006_n__13_VXNE = SISAL_CAST(double, v_ELSE_11011_n__4_p0_o));
              (v_BODY_11006_n__13_XNM = SISAL_CAST(double, v_ELSE_11011_n__6_p0_o));
            }
          }
        }
      }
      bool v_BODY_11006_n__15_p0_o = 0;
      (v_BODY_11006_n__15_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_11005_bodycap_n0_p6 = v_BODY_11006_n__0_VXND);
      (v_LoopB_11005_bodycap_n2_p0 = v_BODY_11006_n__2_I);
      (v_LoopB_11005_bodycap_n6_p0 = v_BODY_11006_n__6_E3);
      (v_LoopB_11005_bodycap_n11_p0 = v_BODY_11006_n__11_XNC);
      (v_LoopB_11005_bodycap_n12_p0 = v_BODY_11006_n__12_XNEI);
      (v_LoopB_11005_bodycap_n13_p0 = v_BODY_11006_n__13_VE3);
      (v_LoopB_11005_bodycap_n13_p1 = v_BODY_11006_n__13_E6);
      (v_LoopB_11005_bodycap_n13_p2 = v_BODY_11006_n__13_VXNE);
      (v_LoopB_11005_bodycap_n13_p3 = v_BODY_11006_n__13_XNM);
      (v_LoopB_11005_bodycap_n15_p0 = v_BODY_11006_n__15_p0_o);
      (v_LoopB_11005_n__5_MERGE_E3 = v_LoopB_11005_bodycap_n6_p0);
      (v_LoopB_11005_n__6_MERGE_E6 = v_LoopB_11005_bodycap_n13_p1);
      (v_LoopB_11005_n__7_MERGE_I = v_LoopB_11005_bodycap_n2_p0);
      (v_LoopB_11005_n__8_MERGE_VE3 = v_LoopB_11005_bodycap_n13_p0);
      (v_LoopB_11005_n__9_MERGE_VXND = v_LoopB_11005_bodycap_n0_p6);
      (v_LoopB_11005_n__10_MERGE_VXNE = v_LoopB_11005_bodycap_n13_p2);
      (v_LoopB_11005_n__11_MERGE_XNC = v_LoopB_11005_bodycap_n11_p0);
      (v_LoopB_11005_n__12_MERGE_XNEI = v_LoopB_11005_bodycap_n12_p0);
      (v_LoopB_11005_n__13_MERGE_XNM = v_LoopB_11005_bodycap_n13_p3);
      (v_LoopB_11005_n__14_MERGE_OLD_E3 = v_LoopB_11005_bodycap_n6_p0);
      (v_LoopB_11005_n__15_MERGE_OLD_E6 = v_LoopB_11005_bodycap_n13_p1);
      (v_LoopB_11005_n__16_MERGE_OLD_I = v_LoopB_11005_bodycap_n2_p0);
      (v_LoopB_11005_n__17_MERGE_OLD_VE3 = v_LoopB_11005_bodycap_n13_p0);
      (v_LoopB_11005_n__18_MERGE_OLD_VXND = v_LoopB_11005_bodycap_n0_p6);
      (v_LoopB_11005_n__19_MERGE_OLD_VXNE = v_LoopB_11005_bodycap_n13_p2);
      (v_LoopB_11005_n__20_MERGE_OLD_XNC = v_LoopB_11005_bodycap_n11_p0);
      (v_LoopB_11005_n__21_MERGE_OLD_XNEI = v_LoopB_11005_bodycap_n12_p0);
      (v_LoopB_11005_n__22_MERGE_OLD_XNM = v_LoopB_11005_bodycap_n13_p3);
      (v_LoopB_11005_n__23_MERGE_first = v_LoopB_11005_bodycap_n15_p0);
      (((double *)v_g1_n__7_p2_o.data)[((int64_t)(__gctr_11005_2++))] = SISAL_CAST(double, v_LoopB_11005_n__18_MERGE_OLD_VXND));
      (((double *)v_g1_n__7_p1_o.data)[((int64_t)(__gctr_11005_1++))] = SISAL_CAST(double, v_LoopB_11005_n__17_MERGE_OLD_VE3));
      (((double *)v_g1_n__7_p0_o.data)[((int64_t)(__gctr_11005_0++))] = SISAL_CAST(double, v_LoopB_11005_n__19_MERGE_OLD_VXNE));
      (v_TEST_11017_n__0_E3 = SISAL_CAST(double, v_LoopB_11005_n__5_MERGE_E3));
      (v_TEST_11017_n__0_E6 = SISAL_CAST(double, v_LoopB_11005_n__6_MERGE_E6));
      (v_TEST_11017_n__0_E6T = SISAL_CAST(double, v_LoopB_11005_n__4_E6T));
      (v_TEST_11017_n__0_I = SISAL_CAST(int32_t, v_LoopB_11005_n__7_MERGE_I));
      (v_TEST_11017_n__0_N = SISAL_CAST(int32_t, v_LoopB_11005_n__0_N));
      (v_TEST_11017_n__0_OLD_E3 = SISAL_CAST(double, v_LoopB_11005_n__14_MERGE_OLD_E3));
      (v_TEST_11017_n__0_OLD_E6 = SISAL_CAST(double, v_LoopB_11005_n__15_MERGE_OLD_E6));
      (v_TEST_11017_n__0_OLD_E6T = SISAL_CAST(double, v_LoopB_11005_n__4_OLD_E6T));
      (v_TEST_11017_n__0_OLD_I = SISAL_CAST(int32_t, v_LoopB_11005_n__16_MERGE_OLD_I));
      (v_TEST_11017_n__0_OLD_VE3 = SISAL_CAST(double, v_LoopB_11005_n__17_MERGE_OLD_VE3));
      (v_TEST_11017_n__0_OLD_VXND = SISAL_CAST(double, v_LoopB_11005_n__18_MERGE_OLD_VXND));
      (v_TEST_11017_n__0_OLD_VXNE = SISAL_CAST(double, v_LoopB_11005_n__19_MERGE_OLD_VXNE));
      (v_TEST_11017_n__0_OLD_XNC = SISAL_CAST(double, v_LoopB_11005_n__20_MERGE_OLD_XNC));
      (v_TEST_11017_n__0_OLD_XNEI = SISAL_CAST(double, v_LoopB_11005_n__21_MERGE_OLD_XNEI));
      (v_TEST_11017_n__0_OLD_XNM = SISAL_CAST(double, v_LoopB_11005_n__22_MERGE_OLD_XNM));
      (v_TEST_11017_n__0_OLD_XNMT = SISAL_CAST(double, v_LoopB_11005_n__4_OLD_XNMT));
      (v_TEST_11017_n__0_VE3 = SISAL_CAST(double, v_LoopB_11005_n__8_MERGE_VE3));
      (v_TEST_11017_n__0_VLIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLIN));
      (v_TEST_11017_n__0_VLR = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VLR));
      (v_TEST_11017_n__0_VSP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSP));
      (v_TEST_11017_n__0_VSTP = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VSTP));
      (v_TEST_11017_n__0_VXND = SISAL_CAST(double, v_LoopB_11005_n__9_MERGE_VXND));
      (v_TEST_11017_n__0_VXNE = SISAL_CAST(double, v_LoopB_11005_n__10_MERGE_VXNE));
      (v_TEST_11017_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_LoopB_11005_n__0_VXNEIN));
      (v_TEST_11017_n__0_XNC = SISAL_CAST(double, v_LoopB_11005_n__11_MERGE_XNC));
      (v_TEST_11017_n__0_XNEI = SISAL_CAST(double, v_LoopB_11005_n__12_MERGE_XNEI));
      (v_TEST_11017_n__0_XNM = SISAL_CAST(double, v_LoopB_11005_n__13_MERGE_XNM));
      (v_TEST_11017_n__0_XNMT = SISAL_CAST(double, v_LoopB_11005_n__4_XNMT));
      (v_TEST_11017_n__1_p0_o = SISAL_CAST(int32_t, 2));
      (v_TEST_11017_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_11017_n__0_I) > SISAL_CAST(int32_t, v_TEST_11017_n__1_p0_o))));
    }
    int32_t v_RETURNS_11016_n__0_p0_o = 0;
    double v_RETURNS_11016_n__0_p1_o = 0;
    int32_t v_RETURNS_11016_n__0_p2_o = 0;
    double v_RETURNS_11016_n__0_p3_o = 0;
    int32_t v_RETURNS_11016_n__0_p4_o = 0;
    double v_RETURNS_11016_n__0_p5_o = 0;
    (v_RETURNS_11016_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_11005_n__0_p6_o));
    (v_RETURNS_11016_n__0_p1_o = SISAL_CAST(double, v_LoopB_11005_n__19_MERGE_OLD_VXNE));
    (v_RETURNS_11016_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_11005_n__0_p7_o));
    (v_RETURNS_11016_n__0_p3_o = SISAL_CAST(double, v_LoopB_11005_n__17_MERGE_OLD_VE3));
    (v_RETURNS_11016_n__0_p4_o = SISAL_CAST(int32_t, v_LoopB_11005_n__0_p8_o));
    (v_RETURNS_11016_n__0_p5_o = SISAL_CAST(double, v_LoopB_11005_n__18_MERGE_OLD_VXND));
    int32_t v_RETURNS_11016_n__2_p0_o = 0;
    (v_RETURNS_11016_n__2_p0_o = SISAL_CAST(int32_t, 1));
    sisal_array_t v_RETURNS_11016_n__3_p0_o = {0};
    (v_RETURNS_11016_n__3_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(double, v_RETURNS_11016_n__0_p1_o)));
    sisal_array_t v_RETURNS_11016_n__1_p0_o = {0};
    (v_RETURNS_11016_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_11016_n__0_p0_o)));
    int32_t v_RETURNS_11016_n__5_p0_o = 0;
    (v_RETURNS_11016_n__5_p0_o = SISAL_CAST(int32_t, 1));
    sisal_array_t v_RETURNS_11016_n__6_p0_o = {0};
    (v_RETURNS_11016_n__6_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(double, v_RETURNS_11016_n__0_p3_o)));
    sisal_array_t v_RETURNS_11016_n__4_p0_o = {0};
    (v_RETURNS_11016_n__4_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_11016_n__0_p0_o)));
    int32_t v_RETURNS_11016_n__8_p0_o = 0;
    (v_RETURNS_11016_n__8_p0_o = SISAL_CAST(int32_t, 1));
    sisal_array_t v_RETURNS_11016_n__9_p0_o = {0};
    (v_RETURNS_11016_n__9_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(double, v_RETURNS_11016_n__0_p5_o)));
    sisal_array_t v_RETURNS_11016_n__7_p0_o = {0};
    (v_RETURNS_11016_n__7_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_11016_n__0_p0_o)));
    (v_g1_n__7_p0_o = SISAL_CAST(sisal_array_t, v_g1_n__7_p0_o));
    (v_g1_n__7_p1_o = SISAL_CAST(sisal_array_t, v_g1_n__7_p1_o));
    (v_g1_n__7_p2_o = SISAL_CAST(sisal_array_t, v_g1_n__7_p2_o));
  }
  (v_g1_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g1_n__7_p0_o));
  (v_g1_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g1_n__7_p1_o));
  (v_g1_n__0_p2_i = SISAL_CAST(sisal_array_t, v_g1_n__7_p2_o));
  struct FUNC_LOOP17_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g1_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g1_n__0_p1_i));
  (__res_obj.res_2 = SISAL_CAST(sisal_array_t, v_g1_n__0_p2_i));
  return __res_obj;
}

extern "C" struct FUNC_MAIN_results func_MAIN(int32_t REP, int32_t N, sisal_array_t VLIN, sisal_array_t VLR, sisal_array_t VSP, sisal_array_t VSTP, sisal_array_t VXNEIN) {
  int32_t v_g2_n__0_N = 0;
  int32_t v_g2_n__0_REP = 0;
  sisal_array_t v_g2_n__0_VLIN = {0};
  sisal_array_t v_g2_n__0_VLR = {0};
  sisal_array_t v_g2_n__0_VSP = {0};
  sisal_array_t v_g2_n__0_VSTP = {0};
  sisal_array_t v_g2_n__0_VXNEIN = {0};
  (v_g2_n__0_REP = SISAL_CAST(int32_t, REP));
  (v_g2_n__0_N = SISAL_CAST(int32_t, N));
  (v_g2_n__0_VLIN = SISAL_CAST(sisal_array_t, VLIN));
  (v_g2_n__0_VLR = SISAL_CAST(sisal_array_t, VLR));
  (v_g2_n__0_VSP = SISAL_CAST(sisal_array_t, VSP));
  (v_g2_n__0_VSTP = SISAL_CAST(sisal_array_t, VSTP));
  (v_g2_n__0_VXNEIN = SISAL_CAST(sisal_array_t, VXNEIN));
  sisal_array_t v_g2_n__0_p0_i = {0};
  sisal_array_t v_g2_n__0_p1_i = {0};
  sisal_array_t v_g2_n__0_p2_i = {0};
  sisal_array_t v_g2_n__1_p0_o = {0};
  sisal_array_t v_g2_n__1_p1_o = {0};
  sisal_array_t v_g2_n__1_p2_o = {0};
  {
    int32_t v_FORALL_10001_n__2_I;
    int32_t v_FORALL_10001_n__0_N = v_g2_n__0_N;
    int32_t v_FORALL_10001_n__0_REP = v_g2_n__0_REP;
    sisal_array_t v_FORALL_10001_n__0_VLIN = v_g2_n__0_VLIN;
    sisal_array_t v_FORALL_10001_n__0_VLR = v_g2_n__0_VLR;
    sisal_array_t v_FORALL_10001_n__0_VSP = v_g2_n__0_VSP;
    sisal_array_t v_FORALL_10001_n__0_VSTP = v_g2_n__0_VSTP;
    sisal_array_t v_FORALL_10001_n__0_VXNEIN = v_g2_n__0_VXNEIN;
    sisal_array_t v_FORALL_10001_n__3___forall_body_0;
    sisal_array_t v_FORALL_10001_n__3___forall_body_1;
    sisal_array_t v_FORALL_10001_n__3___forall_body_2;
    int32_t v_FORALL_10001_n__2___forall_lb_2_0;
    int32_t v_FORALL_10001_n__2___forall_ub_2_0;
    int32_t v_GENERATOR_10003_n__2_I;
    int32_t v_GENERATOR_10003_n__0_N;
    int32_t v_GENERATOR_10003_n__0_REP;
    sisal_array_t v_GENERATOR_10003_n__0_VLIN;
    sisal_array_t v_GENERATOR_10003_n__0_VLR;
    sisal_array_t v_GENERATOR_10003_n__0_VSP;
    sisal_array_t v_GENERATOR_10003_n__0_VSTP;
    sisal_array_t v_GENERATOR_10003_n__0_VXNEIN;
    int32_t v_GENERATOR_10003_n__2___forall_lb_2_0;
    int32_t v_GENERATOR_10003_n__2___forall_ub_2_0;
    int32_t v_BODY_10004_n__0_I;
    int32_t v_BODY_10004_n__0_N;
    int32_t v_BODY_10004_n__0_REP;
    sisal_array_t v_BODY_10004_n__1_V1;
    sisal_array_t v_BODY_10004_n__1_V2;
    sisal_array_t v_BODY_10004_n__1_V3;
    sisal_array_t v_BODY_10004_n__0_VLIN;
    sisal_array_t v_BODY_10004_n__0_VLR;
    sisal_array_t v_BODY_10004_n__0_VSP;
    sisal_array_t v_BODY_10004_n__0_VSTP;
    sisal_array_t v_BODY_10004_n__0_VXNEIN;
    int32_t v_BODY_10004_n__0___forall_lb_2_0;
    int32_t v_BODY_10004_n__0___forall_ub_2_0;
    (v_GENERATOR_10003_n__0_REP = v_FORALL_10001_n__0_REP);
    (v_GENERATOR_10003_n__2___forall_lb_2_0 = 1);
    (v_GENERATOR_10003_n__2___forall_ub_2_0 = v_GENERATOR_10003_n__0_REP);
    for ((v_GENERATOR_10003_n__2_I = 1); (v_GENERATOR_10003_n__2_I <= v_GENERATOR_10003_n__0_REP); (v_GENERATOR_10003_n__2_I++)) {
      (v_BODY_10004_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_10003_n__2_I));
      (v_BODY_10004_n__0_N = SISAL_CAST(int32_t, v_FORALL_10001_n__0_N));
      (v_BODY_10004_n__0_REP = SISAL_CAST(int32_t, v_FORALL_10001_n__0_REP));
      (v_BODY_10004_n__0_VLIN = SISAL_CAST(sisal_array_t, v_FORALL_10001_n__0_VLIN));
      (v_BODY_10004_n__0_VLR = SISAL_CAST(sisal_array_t, v_FORALL_10001_n__0_VLR));
      (v_BODY_10004_n__0_VSP = SISAL_CAST(sisal_array_t, v_FORALL_10001_n__0_VSP));
      (v_BODY_10004_n__0_VSTP = SISAL_CAST(sisal_array_t, v_FORALL_10001_n__0_VSTP));
      (v_BODY_10004_n__0_VXNEIN = SISAL_CAST(sisal_array_t, v_FORALL_10001_n__0_VXNEIN));
      (v_BODY_10004_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10003_n__2___forall_lb_2_0));
      (v_BODY_10004_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_10003_n__2___forall_ub_2_0));
      struct FUNC_LOOP17_results _mr_BODY_10004_1 = func_LOOP17(SISAL_CAST(int32_t, v_BODY_10004_n__0_N), SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_VLIN), SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_VLR), SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_VSP), SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_VSTP), SISAL_CAST(sisal_array_t, v_BODY_10004_n__0_VXNEIN));
      (v_BODY_10004_n__1_V1 = SISAL_CAST(sisal_array_t, _mr_BODY_10004_1.res_0));
      (v_BODY_10004_n__1_V2 = SISAL_CAST(sisal_array_t, _mr_BODY_10004_1.res_1));
      (v_BODY_10004_n__1_V3 = SISAL_CAST(sisal_array_t, _mr_BODY_10004_1.res_2));
      (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_BODY_10004_n__1_V1));
      (v_g2_n__1_p1_o = SISAL_CAST(sisal_array_t, v_BODY_10004_n__1_V2));
      (v_g2_n__1_p2_o = SISAL_CAST(sisal_array_t, v_BODY_10004_n__1_V3));
    }
  }
  (v_g2_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p0_o));
  (v_g2_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p1_o));
  (v_g2_n__0_p2_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p2_o));
  struct FUNC_MAIN_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g2_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g2_n__0_p1_i));
  (__res_obj.res_2 = SISAL_CAST(sisal_array_t, v_g2_n__0_p2_i));
  return __res_obj;
}
