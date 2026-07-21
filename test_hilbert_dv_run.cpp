#define SISAL_CUSTOM_ELEM_SIZE

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <iostream>
#include <dispatch/dispatch.h>
#include <Accelerate/Accelerate.h>
#include <sisal_runtime.h>

struct struct_rec_111 {
  int32_t lo;
  int32_t stride;
  int32_t size;
};
struct struct_rec_110 {
  int32_t stride;
  int32_t size;
};
struct struct_rec_109 {
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
struct FUNC_SGECO_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  double res_2;
  sisal_array_t res_3;
};
struct FUNC_SGEFA_results {
  sisal_array_t res_0;
  sisal_array_t res_1;
  int32_t res_2;
};
struct FUNC_CALC_NEWZY2_results {
  sisal_array_t res_0;
  double res_1;
};
struct FUNC_CALC_NEWZY1_results {
  sisal_array_t res_0;
  double res_1;
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
        case 111:
        case 112:
            return sizeof(struct struct_rec_111);
        case 110:
            return sizeof(struct struct_rec_110);
        case 109:
            return sizeof(struct struct_rec_109);
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
        case 113:
        case 114:
        case 115:
        case 116:
        case 117:
        case 118:
        case 119:
        case 120:
        case 121:
        case 122:
        case 123:
        case 124:
        case 125:
        case 126:
        case 127:
        case 128:
        case 129:
        case 130:
        case 131:
        case 132:
        case 133:
        case 134:
        case 135:
        case 136:
        case 137:
        case 138:
        case 139:
        case 140:
        case 141:
        case 142:
        case 143:
        case 144:
        case 145:
        case 146:
        case 147:
        case 148:
        case 149:
        case 150:
        case 151:
        case 152:
        case 153:
        case 154:
        case 155:
        case 156:
        case 157:
        case 158:
        case 159:
        case 160:
        case 161:
        case 162:
        case 163:
        case 164:
        case 165:
        case 166:
        case 167:
        case 168:
        case 169:
        case 170:
        case 171:
        case 172:
        case 174:
        case 175:
        case 176:
        case 177:
        case 178:
        case 179:
        case 180:
        case 181:
        case 182:
        case 183:
        case 184:
        case 185:
        case 186:
        case 187:
        case 188:
        case 189:
        case 190:
        case 191:
        case 192:
        case 193:
        case 194:
        case 195:
        case 196:
        case 197:
            return sizeof(sisal_array_t);
        case 7:
        case 13:
            return sizeof(int64_t);
        case 2:
        case 6:
        case 10:
        case 95:
        case 173:
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

extern "C" double func_MAIN(sisal_array_t HILBERT, sisal_array_t B);
extern "C" double func_CALC_RESID(sisal_array_t HILB, int32_t N, int32_t LDA, sisal_array_t B);
extern "C" sisal_array_t func_SGESL(sisal_array_t A, int32_t N, sisal_array_t IPVT, sisal_array_t B);
extern "C" struct FUNC_SGECO_results func_SGECO(sisal_array_t A, int32_t LDA, int32_t N);
extern "C" struct FUNC_SGEFA_results func_SGEFA(sisal_array_t A, int32_t LDA, int32_t N);
extern "C" double func_SASUM(int32_t N, sisal_array_t SX);
extern "C" struct FUNC_CALC_NEWZY2_results func_CALC_NEWZY2(int32_t N, sisal_array_t A, sisal_array_t Z, double YNORM);
extern "C" struct FUNC_CALC_NEWZY1_results func_CALC_NEWZY1(int32_t N, sisal_array_t IPVT, sisal_array_t A, sisal_array_t Z);
extern "C" sisal_array_t func_CALC_Z1(sisal_array_t A, int32_t N);
extern "C" sisal_array_t func_CALC_Z3(sisal_array_t A, sisal_array_t Z_IN, sisal_array_t IPVT, int32_t N);
extern "C" double func_SDOT(int32_t START, int32_t COUNT, sisal_array_t SX, sisal_array_t SY);
extern "C" sisal_array_t func_SAXPY(int32_t START, int32_t COUNT, double SCALE, sisal_array_t X, sisal_array_t Y);
extern "C" sisal_array_t func_SSCAL(int32_t START, int32_t COUNT, sisal_array_t SX, double SA);
extern "C" int32_t func_ISAMAX(int32_t START, int32_t COUNT, sisal_array_t SX);
extern "C" sisal_array_t func_TRANSPOSE(sisal_array_t A);
extern "C" double func_SIGN(double A, double B);

extern "C" double func_SIGN(double A, double B) {
  double v_g1_n__0_A = 0;
  double v_g1_n__0_B = 0;
  (v_g1_n__0_A = SISAL_CAST(double, A));
  (v_g1_n__0_B = SISAL_CAST(double, B));
  double v_g1_n__0_p0_i = 0;
  double v_g1_n__1_p0_o = 0;
  double v_IF_DOUBLE___25250_n__0_B = 0;
  (v_IF_DOUBLE___25250_n__0_B = SISAL_CAST(double, v_g1_n__0_B));
  double v_IF_DOUBLE___25250_n__0_A = 0;
  (v_IF_DOUBLE___25250_n__0_A = SISAL_CAST(double, v_g1_n__0_A));
  {
    double v_PREDICATE_25251_n__0_B = 0;
    (v_PREDICATE_25251_n__0_B = SISAL_CAST(double, v_IF_DOUBLE___25250_n__0_B));
    double v_PREDICATE_25251_n__1_p0_o = 0;
    (v_PREDICATE_25251_n__1_p0_o = SISAL_CAST(double, 0.));
    bool v_PREDICATE_25251_n__2_p0_o = 0;
    (v_PREDICATE_25251_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_25251_n__0_B) < SISAL_CAST(double, v_PREDICATE_25251_n__1_p0_o))));
    if (v_PREDICATE_25251_n__2_p0_o) {
      double v_THEN_25253_n__0_A = 0;
      (v_THEN_25253_n__0_A = SISAL_CAST(double, v_IF_DOUBLE___25250_n__0_A));
      double v_THEN_25253_n__1_p0_o = 0;
      (v_THEN_25253_n__1_p0_o = SISAL_CAST(double, 1.));
      double v_THEN_25253_n__2_p0_o = 0;
      (v_THEN_25253_n__2_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_THEN_25253_n__1_p0_o))));
      double v_THEN_25253_n__3_p0_o = 0;
      (v_THEN_25253_n__3_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_THEN_25253_n__0_A))));
      double v_THEN_25253_n__4_p0_o = 0;
      (v_THEN_25253_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_25253_n__2_p0_o) * SISAL_CAST(double, v_THEN_25253_n__3_p0_o))));
      (v_g1_n__1_p0_o = SISAL_CAST(double, v_THEN_25253_n__4_p0_o));
    }
    else {
      double v_ELSE_25252_n__0_A = 0;
      (v_ELSE_25252_n__0_A = SISAL_CAST(double, v_IF_DOUBLE___25250_n__0_A));
      double v_ELSE_25252_n__1_p0_o = 0;
      (v_ELSE_25252_n__1_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_25252_n__0_A))));
      (v_g1_n__1_p0_o = SISAL_CAST(double, v_ELSE_25252_n__1_p0_o));
    }
  }
  (v_g1_n__0_p0_i = SISAL_CAST(double, v_g1_n__1_p0_o));
  return SISAL_CAST(double, v_g1_n__0_p0_i);
}

extern "C" sisal_array_t func_TRANSPOSE(sisal_array_t A) {
  sisal_array_t v_g2_n__0_A = {0};
  (v_g2_n__0_A = SISAL_CAST(sisal_array_t, A));
  sisal_array_t v_g2_n__0_p0_i = {0};
  sisal_array_t v_g2_n__1_p0_o = {0};
  {
    sisal_array_t v_LET_NON_REC_24241_n__0_A = {0};
    int32_t v_LET_NON_REC_24241_n__1_N = 0;
    (v_LET_NON_REC_24241_n__0_A = SISAL_CAST(sisal_array_t, v_g2_n__0_A));
    (v_LET_NON_REC_24241_n__1_N = SISAL_CAST(int32_t, ((int32_t)((SISAL_CAST(sisal_array_t, v_LET_NON_REC_24241_n__0_A).dims[0] > 0) ? SISAL_CAST(sisal_array_t, v_LET_NON_REC_24241_n__0_A).dims[0] : ((int64_t)SISAL_CAST(sisal_array_t, v_LET_NON_REC_24241_n__0_A).size)))));
    sisal_array_t v_LET_NON_REC_24241_n__2_p0_o = {0};
    {
      sisal_array_t v_FORALL_24242_n__0_A = v_LET_NON_REC_24241_n__0_A;
      int32_t v_FORALL_24242_n__2_I;
      int32_t v_FORALL_24242_n__0_N = v_LET_NON_REC_24241_n__1_N;
      sisal_array_t v_FORALL_24242_n__3___forall_body_0;
      int32_t v_FORALL_24242_n__2___forall_lb_2_0;
      int32_t v_FORALL_24242_n__2___forall_ub_2_0;
      sisal_array_t v_GENERATOR_24244_n__0_A;
      int32_t v_GENERATOR_24244_n__2_I;
      int32_t v_GENERATOR_24244_n__0_N;
      int32_t v_GENERATOR_24244_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_24244_n__2___forall_ub_2_0;
      sisal_array_t v_BODY_24245_n__0_A;
      int32_t v_BODY_24245_n__0_I;
      int32_t v_BODY_24245_n__0_N;
      sisal_array_t v_BODY_24245_n__1_ROW;
      int32_t v_BODY_24245_n__0___forall_lb_2_0;
      int32_t v_BODY_24245_n__0___forall_ub_2_0;
      sisal_array_t v_FORALL_24246_n__0_A;
      int32_t v_FORALL_24246_n__0_I;
      int32_t v_FORALL_24246_n__2_J;
      int32_t v_FORALL_24246_n__0_N;
      double v_FORALL_24246_n__3___forall_body_0;
      int32_t v_FORALL_24246_n__2___forall_lb_2_0;
      int32_t v_FORALL_24246_n__2___forall_ub_2_0;
      sisal_array_t v_GENERATOR_24248_n__0_A;
      int32_t v_GENERATOR_24248_n__0_I;
      int32_t v_GENERATOR_24248_n__2_J;
      int32_t v_GENERATOR_24248_n__0_N;
      int32_t v_GENERATOR_24248_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_24248_n__2___forall_ub_2_0;
      sisal_array_t v_BODY_24249_n__0_A;
      int32_t v_BODY_24249_n__0_I;
      int32_t v_BODY_24249_n__0_J;
      int32_t v_BODY_24249_n__0_N;
      int32_t v_BODY_24249_n__0___forall_lb_2_0;
      int32_t v_BODY_24249_n__0___forall_ub_2_0;
      (v_GENERATOR_24244_n__0_N = v_FORALL_24242_n__0_N);
      (v_LET_NON_REC_24241_n__2_p0_o = sisal_array_alloc_sized(1, 94, ((uint64_t)(1 * ((v_GENERATOR_24244_n__0_N - 1) + 1))), sizeof(sisal_array_t)));
      (v_LET_NON_REC_24241_n__2_p0_o.dims[0] = ((v_GENERATOR_24244_n__0_N - 1) + 1));
      (v_LET_NON_REC_24241_n__2_p0_o.lower_bound[0] = 1);
      int32_t __g_24242 = 0;
      (v_GENERATOR_24244_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_24244_n__2___forall_ub_2_0 = v_GENERATOR_24244_n__0_N);
      for ((v_GENERATOR_24244_n__2_I = 1); (v_GENERATOR_24244_n__2_I <= v_GENERATOR_24244_n__0_N); (v_GENERATOR_24244_n__2_I++)) {
        (v_BODY_24245_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_24242_n__0_A));
        (v_BODY_24245_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_24244_n__2_I));
        (v_BODY_24245_n__0_N = SISAL_CAST(int32_t, v_FORALL_24242_n__0_N));
        (v_BODY_24245_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_24244_n__2___forall_lb_2_0));
        (v_BODY_24245_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_24244_n__2___forall_ub_2_0));
        {
          sisal_array_t v_FORALL_24246_n__0_A = v_BODY_24245_n__0_A;
          int32_t v_FORALL_24246_n__0_I = v_BODY_24245_n__0_I;
          int32_t v_FORALL_24246_n__2_J;
          int32_t v_FORALL_24246_n__0_N = v_BODY_24245_n__0_N;
          double v_FORALL_24246_n__3___forall_body_0;
          int32_t v_FORALL_24246_n__2___forall_lb_2_0;
          int32_t v_FORALL_24246_n__2___forall_ub_2_0;
          sisal_array_t v_GENERATOR_24248_n__0_A;
          int32_t v_GENERATOR_24248_n__0_I;
          int32_t v_GENERATOR_24248_n__2_J;
          int32_t v_GENERATOR_24248_n__0_N;
          int32_t v_GENERATOR_24248_n__2___forall_lb_2_0;
          int32_t v_GENERATOR_24248_n__2___forall_ub_2_0;
          sisal_array_t v_BODY_24249_n__0_A;
          int32_t v_BODY_24249_n__0_I;
          int32_t v_BODY_24249_n__0_J;
          int32_t v_BODY_24249_n__0_N;
          int32_t v_BODY_24249_n__0___forall_lb_2_0;
          int32_t v_BODY_24249_n__0___forall_ub_2_0;
          int32_t v_FORALL_24246_n__0_p4_o = v_BODY_24245_n__0___forall_lb_2_0;
          int32_t v_FORALL_24246_n__0_p5_o = v_BODY_24245_n__0___forall_ub_2_0;
          (v_GENERATOR_24248_n__0_N = v_FORALL_24246_n__0_N);
          (v_BODY_24245_n__1_ROW = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_24248_n__0_N - 1) + 1)))));
          (v_BODY_24245_n__1_ROW.dims[0] = ((v_GENERATOR_24248_n__0_N - 1) + 1));
          (v_BODY_24245_n__1_ROW.lower_bound[0] = 1);
          int32_t __g_24246 = 0;
          (v_GENERATOR_24248_n__2___forall_lb_2_0 = 1);
          (v_GENERATOR_24248_n__2___forall_ub_2_0 = v_GENERATOR_24248_n__0_N);
          for ((v_GENERATOR_24248_n__2_J = 1); (v_GENERATOR_24248_n__2_J <= v_GENERATOR_24248_n__0_N); (v_GENERATOR_24248_n__2_J++)) {
            (v_BODY_24249_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_24246_n__0_A));
            (v_BODY_24249_n__0_I = SISAL_CAST(int32_t, v_FORALL_24246_n__0_I));
            (v_BODY_24249_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_24248_n__2_J));
            (v_BODY_24249_n__0_N = SISAL_CAST(int32_t, v_FORALL_24246_n__0_N));
            (v_BODY_24249_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_24248_n__2___forall_lb_2_0));
            (v_BODY_24249_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_24248_n__2___forall_ub_2_0));
            sisal_array_t v_BODY_24249_n__1_p0_o = {0};
            (v_BODY_24249_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_24249_n__0_A), (SISAL_CAST(int32_t, v_BODY_24249_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_24249_n__0_A).lower_bound[0]))));
            double v_BODY_24249_n__2_p0_o = 0;
            (v_BODY_24249_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_24249_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_24249_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_24249_n__1_p0_o).lower_bound[0])]));
            (((double *)v_BODY_24245_n__1_ROW.data)[__g_24246] = SISAL_CAST(double, v_BODY_24249_n__2_p0_o));
            (__g_24246++);
          }
        }
        (((sisal_array_t *)v_LET_NON_REC_24241_n__2_p0_o.data)[__g_24242] = SISAL_CAST(sisal_array_t, v_BODY_24245_n__1_ROW));
        (__g_24242++);
      }
      sisal_array_t __e0_v_LET_NON_REC_24241_n__2_p0_o = ((sisal_array_t *)v_LET_NON_REC_24241_n__2_p0_o.data)[0];
      sisal_array_t __flat_v_LET_NON_REC_24241_n__2_p0_o = sisal_array_alloc_sized((1 + __e0_v_LET_NON_REC_24241_n__2_p0_o.rank), __e0_v_LET_NON_REC_24241_n__2_p0_o.type_id, ((uint64_t)(((uint64_t)(1 * ((v_GENERATOR_24244_n__0_N - 1) + 1))) * __e0_v_LET_NON_REC_24241_n__2_p0_o.size)), sisal_esz(__e0_v_LET_NON_REC_24241_n__2_p0_o));
      (__flat_v_LET_NON_REC_24241_n__2_p0_o.dims[0] = ((v_GENERATOR_24244_n__0_N - 1) + 1));
      (__flat_v_LET_NON_REC_24241_n__2_p0_o.lower_bound[0] = 1);
      for (int32_t __fk_v_LET_NON_REC_24241_n__2_p0_o = 0; (__fk_v_LET_NON_REC_24241_n__2_p0_o < __e0_v_LET_NON_REC_24241_n__2_p0_o.rank); (__fk_v_LET_NON_REC_24241_n__2_p0_o++)) {
        (__flat_v_LET_NON_REC_24241_n__2_p0_o.dims[(1 + __fk_v_LET_NON_REC_24241_n__2_p0_o)] = __e0_v_LET_NON_REC_24241_n__2_p0_o.dims[__fk_v_LET_NON_REC_24241_n__2_p0_o]);
        (__flat_v_LET_NON_REC_24241_n__2_p0_o.lower_bound[(1 + __fk_v_LET_NON_REC_24241_n__2_p0_o)] = __e0_v_LET_NON_REC_24241_n__2_p0_o.lower_bound[__fk_v_LET_NON_REC_24241_n__2_p0_o]);
      }
      for (int32_t __fi_v_LET_NON_REC_24241_n__2_p0_o = 0; (__fi_v_LET_NON_REC_24241_n__2_p0_o < ((int32_t)(1 * ((v_GENERATOR_24244_n__0_N - 1) + 1)))); (__fi_v_LET_NON_REC_24241_n__2_p0_o++)) {
        memcpy((((char *)__flat_v_LET_NON_REC_24241_n__2_p0_o.data) + (((uint64_t)__fi_v_LET_NON_REC_24241_n__2_p0_o) * (__e0_v_LET_NON_REC_24241_n__2_p0_o.size * sisal_esz(__e0_v_LET_NON_REC_24241_n__2_p0_o)))), ((sisal_array_t *)v_LET_NON_REC_24241_n__2_p0_o.data)[__fi_v_LET_NON_REC_24241_n__2_p0_o].data, (__e0_v_LET_NON_REC_24241_n__2_p0_o.size * sisal_esz(__e0_v_LET_NON_REC_24241_n__2_p0_o)));
      }
      (v_LET_NON_REC_24241_n__2_p0_o = __flat_v_LET_NON_REC_24241_n__2_p0_o);
    }
    int32_t v_LET_NON_REC_24241_n__4_p0_o = 0;
    (v_LET_NON_REC_24241_n__4_p0_o = SISAL_CAST(int32_t, 1));
    sisal_array_t v_LET_NON_REC_24241_n__5_p0_o = {0};
    (v_LET_NON_REC_24241_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_setl(SISAL_CAST(sisal_array_t, v_LET_NON_REC_24241_n__2_p0_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_24241_n__4_p0_o)))));
    (v_g2_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_24241_n__5_p0_o));
  }
  (v_g2_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g2_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g2_n__0_p0_i);
}

extern "C" int32_t func_ISAMAX(int32_t START, int32_t COUNT, sisal_array_t SX) {
  int32_t v_g3_n__0_COUNT = 0;
  int32_t v_g3_n__0_START = 0;
  sisal_array_t v_g3_n__0_SX = {0};
  (v_g3_n__0_START = SISAL_CAST(int32_t, START));
  (v_g3_n__0_COUNT = SISAL_CAST(int32_t, COUNT));
  (v_g3_n__0_SX = SISAL_CAST(sisal_array_t, SX));
  int32_t v_g3_n__0_p0_i = 0;
  int32_t v_g3_n__1_p0_o = 0;
  {
    int32_t v_LET_NON_REC_23228_n__0_COUNT = 0;
    int32_t v_LET_NON_REC_23228_n__4_INDEX = 0;
    double v_LET_NON_REC_23228_n__2_MAX_VAL = 0;
    int32_t v_LET_NON_REC_23228_n__0_START = 0;
    sisal_array_t v_LET_NON_REC_23228_n__0_SX = {0};
    (v_LET_NON_REC_23228_n__0_COUNT = SISAL_CAST(int32_t, v_g3_n__0_COUNT));
    (v_LET_NON_REC_23228_n__0_START = SISAL_CAST(int32_t, v_g3_n__0_START));
    (v_LET_NON_REC_23228_n__0_SX = SISAL_CAST(sisal_array_t, v_g3_n__0_SX));
    double v_LET_NON_REC_23228_n__1_p0_o = 0;
    {
      int32_t v_FORALL_23229_n__0_COUNT = v_LET_NON_REC_23228_n__0_COUNT;
      int32_t v_FORALL_23229_n__2_I;
      int32_t v_FORALL_23229_n__0_START = v_LET_NON_REC_23228_n__0_START;
      sisal_array_t v_FORALL_23229_n__0_SX = v_LET_NON_REC_23228_n__0_SX;
      double v_FORALL_23229_n__3___forall_body_0;
      int32_t v_FORALL_23229_n__2___forall_lb_2_0;
      int32_t v_FORALL_23229_n__2___forall_ub_2_0;
      int32_t v_GENERATOR_23231_n__0_COUNT;
      int32_t v_GENERATOR_23231_n__2_I;
      int32_t v_GENERATOR_23231_n__0_START;
      sisal_array_t v_GENERATOR_23231_n__0_SX;
      int32_t v_GENERATOR_23231_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_23231_n__2___forall_ub_2_0;
      int32_t v_BODY_23232_n__0_COUNT;
      int32_t v_BODY_23232_n__0_I;
      int32_t v_BODY_23232_n__0_START;
      sisal_array_t v_BODY_23232_n__0_SX;
      int32_t v_BODY_23232_n__0___forall_lb_2_0;
      int32_t v_BODY_23232_n__0___forall_ub_2_0;
      (v_GENERATOR_23231_n__0_COUNT = v_FORALL_23229_n__0_COUNT);
      (v_LET_NON_REC_23228_n__1_p0_o = (-1e308));
      (v_GENERATOR_23231_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_23231_n__2___forall_ub_2_0 = v_GENERATOR_23231_n__0_COUNT);
      for ((v_GENERATOR_23231_n__2_I = 1); (v_GENERATOR_23231_n__2_I <= v_GENERATOR_23231_n__0_COUNT); (v_GENERATOR_23231_n__2_I++)) {
        (v_BODY_23232_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_23229_n__0_COUNT));
        (v_BODY_23232_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_23231_n__2_I));
        (v_BODY_23232_n__0_START = SISAL_CAST(int32_t, v_FORALL_23229_n__0_START));
        (v_BODY_23232_n__0_SX = SISAL_CAST(sisal_array_t, v_FORALL_23229_n__0_SX));
        (v_BODY_23232_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_23231_n__2___forall_lb_2_0));
        (v_BODY_23232_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_23231_n__2___forall_ub_2_0));
        int32_t v_BODY_23232_n__1_p0_o = 0;
        (v_BODY_23232_n__1_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_23232_n__0_I) + SISAL_CAST(int32_t, v_BODY_23232_n__0_START))));
        int32_t v_BODY_23232_n__2_p0_o = 0;
        (v_BODY_23232_n__2_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_23232_n__3_p0_o = 0;
        (v_BODY_23232_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_23232_n__1_p0_o) - SISAL_CAST(int32_t, v_BODY_23232_n__2_p0_o))));
        float v_BODY_23232_n__4_p0_o = 0;
        (v_BODY_23232_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_23232_n__0_SX).data)[(SISAL_CAST(int32_t, v_BODY_23232_n__3_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_23232_n__0_SX).lower_bound[0])]));
        int32_t v_BODY_23232_n__5_p0_o = 0;
        (v_BODY_23232_n__5_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_23232_n__0_I) + SISAL_CAST(int32_t, v_BODY_23232_n__0_START))));
        int32_t v_BODY_23232_n__6_p0_o = 0;
        (v_BODY_23232_n__6_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_23232_n__7_p0_o = 0;
        (v_BODY_23232_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_23232_n__5_p0_o) - SISAL_CAST(int32_t, v_BODY_23232_n__6_p0_o))));
        double v_BODY_23232_n__8_p0_o = 0;
        (v_BODY_23232_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_23232_n__0_SX).data)[(SISAL_CAST(int32_t, v_BODY_23232_n__7_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_23232_n__0_SX).lower_bound[0])]));
        double v_BODY_23232_n__9_p0_o = 0;
        (v_BODY_23232_n__9_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_23232_n__8_p0_o))));
        if ((SISAL_CAST(double, v_BODY_23232_n__9_p0_o) > v_LET_NON_REC_23228_n__1_p0_o)) {
          (v_LET_NON_REC_23228_n__1_p0_o = SISAL_CAST(double, v_BODY_23232_n__9_p0_o));
        }
      }
    }
    int32_t v_LET_NON_REC_23228_n__3_p0_o = 0;
    {
      int32_t v_FORALL_23233_n__0_COUNT = v_LET_NON_REC_23228_n__0_COUNT;
      int32_t v_FORALL_23233_n__2_J;
      double v_FORALL_23233_n__0_MAX_VAL = v_LET_NON_REC_23228_n__1_p0_o;
      int32_t v_FORALL_23233_n__0_START = v_LET_NON_REC_23228_n__0_START;
      sisal_array_t v_FORALL_23233_n__0_SX = v_LET_NON_REC_23228_n__0_SX;
      int32_t v_FORALL_23233_n__3___forall_body_0;
      int32_t v_FORALL_23233_n__2___forall_lb_2_0;
      int32_t v_FORALL_23233_n__2___forall_ub_2_0;
      int32_t v_GENERATOR_23235_n__0_COUNT;
      int32_t v_GENERATOR_23235_n__2_J;
      double v_GENERATOR_23235_n__0_MAX_VAL;
      int32_t v_GENERATOR_23235_n__0_START;
      sisal_array_t v_GENERATOR_23235_n__0_SX;
      int32_t v_GENERATOR_23235_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_23235_n__2___forall_ub_2_0;
      int32_t v_BODY_23236_n__0_COUNT;
      int32_t v_BODY_23236_n__0_J;
      double v_BODY_23236_n__0_MAX_VAL;
      int32_t v_BODY_23236_n__0_START;
      sisal_array_t v_BODY_23236_n__0_SX;
      int32_t v_BODY_23236_n__0___forall_lb_2_0;
      int32_t v_BODY_23236_n__0___forall_ub_2_0;
      int32_t v_IF_INTEGRAL___23237_n__0_COUNT;
      int32_t v_IF_INTEGRAL___23237_n__0_J;
      double v_IF_INTEGRAL___23237_n__0_MAX_VAL;
      int32_t v_IF_INTEGRAL___23237_n__0_START;
      sisal_array_t v_IF_INTEGRAL___23237_n__0_SX;
      int32_t v_PREDICATE_23238_n__0_J;
      double v_PREDICATE_23238_n__0_MAX_VAL;
      int32_t v_PREDICATE_23238_n__0_START;
      sisal_array_t v_PREDICATE_23238_n__0_SX;
      int32_t v_ELSE_23239_n__0_COUNT;
      int32_t v_THEN_23240_n__0_J;
      (v_GENERATOR_23235_n__0_COUNT = v_FORALL_23233_n__0_COUNT);
      (v_LET_NON_REC_23228_n__3_p0_o = 0x7fffffff);
      (v_GENERATOR_23235_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_23235_n__2___forall_ub_2_0 = v_GENERATOR_23235_n__0_COUNT);
      for ((v_GENERATOR_23235_n__2_J = 1); (v_GENERATOR_23235_n__2_J <= v_GENERATOR_23235_n__0_COUNT); (v_GENERATOR_23235_n__2_J++)) {
        (v_BODY_23236_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_23233_n__0_COUNT));
        (v_BODY_23236_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_23235_n__2_J));
        (v_BODY_23236_n__0_MAX_VAL = SISAL_CAST(double, v_FORALL_23233_n__0_MAX_VAL));
        (v_BODY_23236_n__0_START = SISAL_CAST(int32_t, v_FORALL_23233_n__0_START));
        (v_BODY_23236_n__0_SX = SISAL_CAST(sisal_array_t, v_FORALL_23233_n__0_SX));
        (v_BODY_23236_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_23235_n__2___forall_lb_2_0));
        (v_BODY_23236_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_23235_n__2___forall_ub_2_0));
        int32_t v_BODY_23236_n__1_p0_o = 0;
        (v_IF_INTEGRAL___23237_n__0_SX = SISAL_CAST(sisal_array_t, v_BODY_23236_n__0_SX));
        (v_IF_INTEGRAL___23237_n__0_J = SISAL_CAST(int32_t, v_BODY_23236_n__0_J));
        (v_IF_INTEGRAL___23237_n__0_START = SISAL_CAST(int32_t, v_BODY_23236_n__0_START));
        (v_IF_INTEGRAL___23237_n__0_MAX_VAL = SISAL_CAST(double, v_BODY_23236_n__0_MAX_VAL));
        (v_IF_INTEGRAL___23237_n__0_COUNT = SISAL_CAST(int32_t, v_BODY_23236_n__0_COUNT));
        {
          (v_PREDICATE_23238_n__0_SX = SISAL_CAST(sisal_array_t, v_IF_INTEGRAL___23237_n__0_SX));
          (v_PREDICATE_23238_n__0_J = SISAL_CAST(int32_t, v_IF_INTEGRAL___23237_n__0_J));
          (v_PREDICATE_23238_n__0_START = SISAL_CAST(int32_t, v_IF_INTEGRAL___23237_n__0_START));
          (v_PREDICATE_23238_n__0_MAX_VAL = SISAL_CAST(double, v_IF_INTEGRAL___23237_n__0_MAX_VAL));
          int32_t v_PREDICATE_23238_n__1_p0_o = 0;
          (v_PREDICATE_23238_n__1_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_PREDICATE_23238_n__0_J) + SISAL_CAST(int32_t, v_PREDICATE_23238_n__0_START))));
          int32_t v_PREDICATE_23238_n__2_p0_o = 0;
          (v_PREDICATE_23238_n__2_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_PREDICATE_23238_n__3_p0_o = 0;
          (v_PREDICATE_23238_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_PREDICATE_23238_n__1_p0_o) - SISAL_CAST(int32_t, v_PREDICATE_23238_n__2_p0_o))));
          float v_PREDICATE_23238_n__4_p0_o = 0;
          (v_PREDICATE_23238_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_PREDICATE_23238_n__0_SX).data)[(SISAL_CAST(int32_t, v_PREDICATE_23238_n__3_p0_o) - SISAL_CAST(sisal_array_t, v_PREDICATE_23238_n__0_SX).lower_bound[0])]));
          int32_t v_PREDICATE_23238_n__5_p0_o = 0;
          (v_PREDICATE_23238_n__5_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_PREDICATE_23238_n__0_J) + SISAL_CAST(int32_t, v_PREDICATE_23238_n__0_START))));
          int32_t v_PREDICATE_23238_n__6_p0_o = 0;
          (v_PREDICATE_23238_n__6_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_PREDICATE_23238_n__7_p0_o = 0;
          (v_PREDICATE_23238_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_PREDICATE_23238_n__5_p0_o) - SISAL_CAST(int32_t, v_PREDICATE_23238_n__6_p0_o))));
          double v_PREDICATE_23238_n__8_p0_o = 0;
          (v_PREDICATE_23238_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_23238_n__0_SX).data)[(SISAL_CAST(int32_t, v_PREDICATE_23238_n__7_p0_o) - SISAL_CAST(sisal_array_t, v_PREDICATE_23238_n__0_SX).lower_bound[0])]));
          double v_PREDICATE_23238_n__9_p0_o = 0;
          (v_PREDICATE_23238_n__9_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_23238_n__8_p0_o))));
          bool v_PREDICATE_23238_n__10_p0_o = 0;
          (v_PREDICATE_23238_n__10_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_23238_n__9_p0_o) == SISAL_CAST(double, v_PREDICATE_23238_n__0_MAX_VAL))));
          if (v_PREDICATE_23238_n__10_p0_o) {
            (v_THEN_23240_n__0_J = SISAL_CAST(int32_t, v_IF_INTEGRAL___23237_n__0_J));
            (v_BODY_23236_n__1_p0_o = SISAL_CAST(int32_t, v_THEN_23240_n__0_J));
          }
          else {
            (v_ELSE_23239_n__0_COUNT = SISAL_CAST(int32_t, v_IF_INTEGRAL___23237_n__0_COUNT));
            (v_BODY_23236_n__1_p0_o = SISAL_CAST(int32_t, v_ELSE_23239_n__0_COUNT));
          }
        }
        if ((SISAL_CAST(int32_t, v_BODY_23236_n__1_p0_o) < v_LET_NON_REC_23228_n__3_p0_o)) {
          (v_LET_NON_REC_23228_n__3_p0_o = SISAL_CAST(int32_t, v_BODY_23236_n__1_p0_o));
        }
      }
    }
    (v_g3_n__1_p0_o = SISAL_CAST(int32_t, v_LET_NON_REC_23228_n__3_p0_o));
  }
  (v_g3_n__0_p0_i = SISAL_CAST(int32_t, v_g3_n__1_p0_o));
  return SISAL_CAST(int32_t, v_g3_n__0_p0_i);
}

extern "C" sisal_array_t func_SSCAL(int32_t START, int32_t COUNT, sisal_array_t SX, double SA) {
  int32_t v_g4_n__0_COUNT = 0;
  double v_g4_n__0_SA = 0;
  int32_t v_g4_n__0_START = 0;
  sisal_array_t v_g4_n__0_SX = {0};
  (v_g4_n__0_START = SISAL_CAST(int32_t, START));
  (v_g4_n__0_COUNT = SISAL_CAST(int32_t, COUNT));
  (v_g4_n__0_SX = SISAL_CAST(sisal_array_t, SX));
  (v_g4_n__0_SA = SISAL_CAST(double, SA));
  sisal_array_t v_g4_n__0_p0_i = {0};
  sisal_array_t v_g4_n__1_p0_o = {0};
  {
    int32_t v_LET_NON_REC_22219_n__0_COUNT = 0;
    double v_LET_NON_REC_22219_n__0_SA = 0;
    sisal_array_t v_LET_NON_REC_22219_n__4_SCALED_VECTOR = {0};
    int32_t v_LET_NON_REC_22219_n__0_START = 0;
    sisal_array_t v_LET_NON_REC_22219_n__0_SX = {0};
    sisal_array_t v_LET_NON_REC_22219_n__2_UC = {0};
    (v_LET_NON_REC_22219_n__0_COUNT = SISAL_CAST(int32_t, v_g4_n__0_COUNT));
    (v_LET_NON_REC_22219_n__0_SA = SISAL_CAST(double, v_g4_n__0_SA));
    (v_LET_NON_REC_22219_n__0_START = SISAL_CAST(int32_t, v_g4_n__0_START));
    (v_LET_NON_REC_22219_n__0_SX = SISAL_CAST(sisal_array_t, v_g4_n__0_SX));
    sisal_array_t v_LET_NON_REC_22219_n__1_p0_o = {0};
    {
      int32_t v_FORALL_22220_n__0_COUNT = v_LET_NON_REC_22219_n__0_COUNT;
      int32_t v_FORALL_22220_n__2_I;
      double v_FORALL_22220_n__0_SA = v_LET_NON_REC_22219_n__0_SA;
      int32_t v_FORALL_22220_n__0_START = v_LET_NON_REC_22219_n__0_START;
      sisal_array_t v_FORALL_22220_n__0_SX = v_LET_NON_REC_22219_n__0_SX;
      double v_FORALL_22220_n__3___forall_body_0;
      int32_t v_FORALL_22220_n__2___forall_lb_4_0;
      int32_t v_FORALL_22220_n__2___forall_ub_4_0;
      int32_t v_GENERATOR_22222_n__0_COUNT;
      int32_t v_GENERATOR_22222_n__4_I;
      double v_GENERATOR_22222_n__0_SA;
      int32_t v_GENERATOR_22222_n__0_START;
      sisal_array_t v_GENERATOR_22222_n__0_SX;
      int32_t v_GENERATOR_22222_n__4___forall_lb_4_0;
      int32_t v_GENERATOR_22222_n__4___forall_ub_4_0;
      int32_t v_BODY_22223_n__0_COUNT;
      int32_t v_BODY_22223_n__0_I;
      double v_BODY_22223_n__0_SA;
      int32_t v_BODY_22223_n__0_START;
      sisal_array_t v_BODY_22223_n__0_SX;
      int32_t v_BODY_22223_n__0___forall_lb_4_0;
      int32_t v_BODY_22223_n__0___forall_ub_4_0;
      (v_GENERATOR_22222_n__0_START = v_FORALL_22220_n__0_START);
      int32_t v_GENERATOR_22222_n__3_p0_o = 0;
      (v_GENERATOR_22222_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_GENERATOR_22222_n__0_START) - SISAL_CAST(int32_t, 1))));
      (v_LET_NON_REC_22219_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_22222_n__3_p0_o - 1) + 1)))));
      (v_LET_NON_REC_22219_n__1_p0_o.dims[0] = ((v_GENERATOR_22222_n__3_p0_o - 1) + 1));
      (v_LET_NON_REC_22219_n__1_p0_o.lower_bound[0] = 1);
      int32_t __g_22220 = 0;
      (v_GENERATOR_22222_n__4___forall_lb_4_0 = 1);
      (v_GENERATOR_22222_n__4___forall_ub_4_0 = v_GENERATOR_22222_n__3_p0_o);
      for ((v_GENERATOR_22222_n__4_I = 1); (v_GENERATOR_22222_n__4_I <= v_GENERATOR_22222_n__3_p0_o); (v_GENERATOR_22222_n__4_I++)) {
        (v_BODY_22223_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_22220_n__0_COUNT));
        (v_BODY_22223_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_22222_n__4_I));
        (v_BODY_22223_n__0_SA = SISAL_CAST(double, v_FORALL_22220_n__0_SA));
        (v_BODY_22223_n__0_START = SISAL_CAST(int32_t, v_FORALL_22220_n__0_START));
        (v_BODY_22223_n__0_SX = SISAL_CAST(sisal_array_t, v_FORALL_22220_n__0_SX));
        (v_BODY_22223_n__0___forall_lb_4_0 = SISAL_CAST(int32_t, v_GENERATOR_22222_n__4___forall_lb_4_0));
        (v_BODY_22223_n__0___forall_ub_4_0 = SISAL_CAST(int32_t, v_GENERATOR_22222_n__4___forall_ub_4_0));
        double v_BODY_22223_n__1_p0_o = 0;
        (v_BODY_22223_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_22223_n__0_SX).data)[(SISAL_CAST(int32_t, v_BODY_22223_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_22223_n__0_SX).lower_bound[0])]));
        (((double *)v_LET_NON_REC_22219_n__1_p0_o.data)[__g_22220] = SISAL_CAST(double, v_BODY_22223_n__1_p0_o));
        (__g_22220++);
      }
    }
    sisal_array_t v_LET_NON_REC_22219_n__3_p0_o = {0};
    {
      int32_t v_FORALL_22224_n__0_COUNT = v_LET_NON_REC_22219_n__0_COUNT;
      int32_t v_FORALL_22224_n__2_I;
      double v_FORALL_22224_n__0_SA = v_LET_NON_REC_22219_n__0_SA;
      int32_t v_FORALL_22224_n__0_START = v_LET_NON_REC_22219_n__0_START;
      sisal_array_t v_FORALL_22224_n__0_SX = v_LET_NON_REC_22219_n__0_SX;
      sisal_array_t v_FORALL_22224_n__0_UC = v_LET_NON_REC_22219_n__1_p0_o;
      double v_FORALL_22224_n__3___forall_body_0;
      int32_t v_FORALL_22224_n__2___forall_lb_2_0;
      int32_t v_FORALL_22224_n__2___forall_ub_2_0;
      int32_t v_GENERATOR_22226_n__0_COUNT;
      int32_t v_GENERATOR_22226_n__2_I;
      double v_GENERATOR_22226_n__0_SA;
      int32_t v_GENERATOR_22226_n__0_START;
      sisal_array_t v_GENERATOR_22226_n__0_SX;
      sisal_array_t v_GENERATOR_22226_n__0_UC;
      int32_t v_GENERATOR_22226_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_22226_n__2___forall_ub_2_0;
      int32_t v_BODY_22227_n__0_COUNT;
      int32_t v_BODY_22227_n__0_I;
      double v_BODY_22227_n__0_SA;
      int32_t v_BODY_22227_n__0_START;
      sisal_array_t v_BODY_22227_n__0_SX;
      sisal_array_t v_BODY_22227_n__0_UC;
      int32_t v_BODY_22227_n__0___forall_lb_2_0;
      int32_t v_BODY_22227_n__0___forall_ub_2_0;
      (v_GENERATOR_22226_n__0_COUNT = v_FORALL_22224_n__0_COUNT);
      (v_LET_NON_REC_22219_n__3_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_22226_n__0_COUNT - 1) + 1)))));
      (v_LET_NON_REC_22219_n__3_p0_o.dims[0] = ((v_GENERATOR_22226_n__0_COUNT - 1) + 1));
      (v_LET_NON_REC_22219_n__3_p0_o.lower_bound[0] = 1);
      int32_t __g_22224 = 0;
      (v_GENERATOR_22226_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_22226_n__2___forall_ub_2_0 = v_GENERATOR_22226_n__0_COUNT);
      for ((v_GENERATOR_22226_n__2_I = 1); (v_GENERATOR_22226_n__2_I <= v_GENERATOR_22226_n__0_COUNT); (v_GENERATOR_22226_n__2_I++)) {
        (v_BODY_22227_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_22224_n__0_COUNT));
        (v_BODY_22227_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_22226_n__2_I));
        (v_BODY_22227_n__0_SA = SISAL_CAST(double, v_FORALL_22224_n__0_SA));
        (v_BODY_22227_n__0_START = SISAL_CAST(int32_t, v_FORALL_22224_n__0_START));
        (v_BODY_22227_n__0_SX = SISAL_CAST(sisal_array_t, v_FORALL_22224_n__0_SX));
        (v_BODY_22227_n__0_UC = SISAL_CAST(sisal_array_t, v_FORALL_22224_n__0_UC));
        (v_BODY_22227_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_22226_n__2___forall_lb_2_0));
        (v_BODY_22227_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_22226_n__2___forall_ub_2_0));
        int32_t v_BODY_22227_n__1_p0_o = 0;
        (v_BODY_22227_n__1_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_22227_n__0_I) + SISAL_CAST(int32_t, v_BODY_22227_n__0_START))));
        int32_t v_BODY_22227_n__2_p0_o = 0;
        (v_BODY_22227_n__2_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_22227_n__3_p0_o = 0;
        (v_BODY_22227_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_22227_n__1_p0_o) - SISAL_CAST(int32_t, v_BODY_22227_n__2_p0_o))));
        double v_BODY_22227_n__4_p0_o = 0;
        (v_BODY_22227_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_22227_n__0_SX).data)[(SISAL_CAST(int32_t, v_BODY_22227_n__3_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_22227_n__0_SX).lower_bound[0])]));
        double v_BODY_22227_n__5_p0_o = 0;
        (v_BODY_22227_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_22227_n__0_SA) * SISAL_CAST(double, v_BODY_22227_n__4_p0_o))));
        (((double *)v_LET_NON_REC_22219_n__3_p0_o.data)[__g_22224] = SISAL_CAST(double, v_BODY_22227_n__5_p0_o));
        (__g_22224++);
      }
    }
    sisal_array_t v_LET_NON_REC_22219_n__5_p0_o = {0};
    (v_LET_NON_REC_22219_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_addh_arr(SISAL_CAST(sisal_array_t, v_LET_NON_REC_22219_n__1_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_22219_n__3_p0_o))));
    (v_g4_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_22219_n__5_p0_o));
  }
  (v_g4_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g4_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g4_n__0_p0_i);
}

extern "C" sisal_array_t func_SAXPY(int32_t START, int32_t COUNT, double SCALE, sisal_array_t X, sisal_array_t Y) {
  int32_t v_g5_n__0_COUNT = 0;
  double v_g5_n__0_SCALE = 0;
  int32_t v_g5_n__0_START = 0;
  sisal_array_t v_g5_n__0_X = {0};
  sisal_array_t v_g5_n__0_Y = {0};
  (v_g5_n__0_START = SISAL_CAST(int32_t, START));
  (v_g5_n__0_COUNT = SISAL_CAST(int32_t, COUNT));
  (v_g5_n__0_SCALE = SISAL_CAST(double, SCALE));
  (v_g5_n__0_X = SISAL_CAST(sisal_array_t, X));
  (v_g5_n__0_Y = SISAL_CAST(sisal_array_t, Y));
  sisal_array_t v_g5_n__0_p0_i = {0};
  sisal_array_t v_g5_n__1_p0_o = {0};
  {
    int32_t v_LET_NON_REC_21210_n__0_COUNT = 0;
    sisal_array_t v_LET_NON_REC_21210_n__4_RESULT = {0};
    double v_LET_NON_REC_21210_n__0_SCALE = 0;
    int32_t v_LET_NON_REC_21210_n__0_START = 0;
    sisal_array_t v_LET_NON_REC_21210_n__2_UC = {0};
    sisal_array_t v_LET_NON_REC_21210_n__0_X = {0};
    sisal_array_t v_LET_NON_REC_21210_n__0_Y = {0};
    (v_LET_NON_REC_21210_n__0_COUNT = SISAL_CAST(int32_t, v_g5_n__0_COUNT));
    (v_LET_NON_REC_21210_n__0_SCALE = SISAL_CAST(double, v_g5_n__0_SCALE));
    (v_LET_NON_REC_21210_n__0_START = SISAL_CAST(int32_t, v_g5_n__0_START));
    (v_LET_NON_REC_21210_n__0_X = SISAL_CAST(sisal_array_t, v_g5_n__0_X));
    (v_LET_NON_REC_21210_n__0_Y = SISAL_CAST(sisal_array_t, v_g5_n__0_Y));
    sisal_array_t v_LET_NON_REC_21210_n__1_p0_o = {0};
    {
      int32_t v_FORALL_21211_n__0_COUNT = v_LET_NON_REC_21210_n__0_COUNT;
      int32_t v_FORALL_21211_n__2_I;
      double v_FORALL_21211_n__0_SCALE = v_LET_NON_REC_21210_n__0_SCALE;
      int32_t v_FORALL_21211_n__0_START = v_LET_NON_REC_21210_n__0_START;
      sisal_array_t v_FORALL_21211_n__0_X = v_LET_NON_REC_21210_n__0_X;
      sisal_array_t v_FORALL_21211_n__0_Y = v_LET_NON_REC_21210_n__0_Y;
      double v_FORALL_21211_n__3___forall_body_0;
      int32_t v_FORALL_21211_n__2___forall_lb_4_0;
      int32_t v_FORALL_21211_n__2___forall_ub_4_0;
      int32_t v_GENERATOR_21213_n__0_COUNT;
      int32_t v_GENERATOR_21213_n__4_I;
      double v_GENERATOR_21213_n__0_SCALE;
      int32_t v_GENERATOR_21213_n__0_START;
      sisal_array_t v_GENERATOR_21213_n__0_X;
      sisal_array_t v_GENERATOR_21213_n__0_Y;
      int32_t v_GENERATOR_21213_n__4___forall_lb_4_0;
      int32_t v_GENERATOR_21213_n__4___forall_ub_4_0;
      int32_t v_BODY_21214_n__0_COUNT;
      int32_t v_BODY_21214_n__0_I;
      double v_BODY_21214_n__0_SCALE;
      int32_t v_BODY_21214_n__0_START;
      sisal_array_t v_BODY_21214_n__0_X;
      sisal_array_t v_BODY_21214_n__0_Y;
      int32_t v_BODY_21214_n__0___forall_lb_4_0;
      int32_t v_BODY_21214_n__0___forall_ub_4_0;
      (v_GENERATOR_21213_n__0_START = v_FORALL_21211_n__0_START);
      int32_t v_GENERATOR_21213_n__3_p0_o = 0;
      (v_GENERATOR_21213_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_GENERATOR_21213_n__0_START) - SISAL_CAST(int32_t, 1))));
      (v_LET_NON_REC_21210_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_21213_n__3_p0_o - 1) + 1)))));
      (v_LET_NON_REC_21210_n__1_p0_o.dims[0] = ((v_GENERATOR_21213_n__3_p0_o - 1) + 1));
      (v_LET_NON_REC_21210_n__1_p0_o.lower_bound[0] = 1);
      int32_t __g_21211 = 0;
      (v_GENERATOR_21213_n__4___forall_lb_4_0 = 1);
      (v_GENERATOR_21213_n__4___forall_ub_4_0 = v_GENERATOR_21213_n__3_p0_o);
      for ((v_GENERATOR_21213_n__4_I = 1); (v_GENERATOR_21213_n__4_I <= v_GENERATOR_21213_n__3_p0_o); (v_GENERATOR_21213_n__4_I++)) {
        (v_BODY_21214_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_21211_n__0_COUNT));
        (v_BODY_21214_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_21213_n__4_I));
        (v_BODY_21214_n__0_SCALE = SISAL_CAST(double, v_FORALL_21211_n__0_SCALE));
        (v_BODY_21214_n__0_START = SISAL_CAST(int32_t, v_FORALL_21211_n__0_START));
        (v_BODY_21214_n__0_X = SISAL_CAST(sisal_array_t, v_FORALL_21211_n__0_X));
        (v_BODY_21214_n__0_Y = SISAL_CAST(sisal_array_t, v_FORALL_21211_n__0_Y));
        (v_BODY_21214_n__0___forall_lb_4_0 = SISAL_CAST(int32_t, v_GENERATOR_21213_n__4___forall_lb_4_0));
        (v_BODY_21214_n__0___forall_ub_4_0 = SISAL_CAST(int32_t, v_GENERATOR_21213_n__4___forall_ub_4_0));
        double v_BODY_21214_n__1_p0_o = 0;
        (v_BODY_21214_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_21214_n__0_Y).data)[(SISAL_CAST(int32_t, v_BODY_21214_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_21214_n__0_Y).lower_bound[0])]));
        (((double *)v_LET_NON_REC_21210_n__1_p0_o.data)[__g_21211] = SISAL_CAST(double, v_BODY_21214_n__1_p0_o));
        (__g_21211++);
      }
    }
    sisal_array_t v_LET_NON_REC_21210_n__3_p0_o = {0};
    {
      int32_t v_FORALL_21215_n__0_COUNT = v_LET_NON_REC_21210_n__0_COUNT;
      int32_t v_FORALL_21215_n__2_I;
      double v_FORALL_21215_n__0_SCALE = v_LET_NON_REC_21210_n__0_SCALE;
      int32_t v_FORALL_21215_n__0_START = v_LET_NON_REC_21210_n__0_START;
      sisal_array_t v_FORALL_21215_n__0_UC = v_LET_NON_REC_21210_n__1_p0_o;
      sisal_array_t v_FORALL_21215_n__0_X = v_LET_NON_REC_21210_n__0_X;
      sisal_array_t v_FORALL_21215_n__0_Y = v_LET_NON_REC_21210_n__0_Y;
      double v_FORALL_21215_n__3___forall_body_0;
      int32_t v_FORALL_21215_n__2___forall_lb_2_0;
      int32_t v_FORALL_21215_n__2___forall_ub_2_0;
      int32_t v_GENERATOR_21217_n__0_COUNT;
      int32_t v_GENERATOR_21217_n__2_I;
      double v_GENERATOR_21217_n__0_SCALE;
      int32_t v_GENERATOR_21217_n__0_START;
      sisal_array_t v_GENERATOR_21217_n__0_UC;
      sisal_array_t v_GENERATOR_21217_n__0_X;
      sisal_array_t v_GENERATOR_21217_n__0_Y;
      int32_t v_GENERATOR_21217_n__2___forall_lb_2_0;
      int32_t v_GENERATOR_21217_n__2___forall_ub_2_0;
      int32_t v_BODY_21218_n__0_COUNT;
      int32_t v_BODY_21218_n__0_I;
      double v_BODY_21218_n__0_SCALE;
      int32_t v_BODY_21218_n__0_START;
      sisal_array_t v_BODY_21218_n__0_UC;
      sisal_array_t v_BODY_21218_n__0_X;
      sisal_array_t v_BODY_21218_n__0_Y;
      int32_t v_BODY_21218_n__0___forall_lb_2_0;
      int32_t v_BODY_21218_n__0___forall_ub_2_0;
      (v_GENERATOR_21217_n__0_COUNT = v_FORALL_21215_n__0_COUNT);
      (v_LET_NON_REC_21210_n__3_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_21217_n__0_COUNT - 1) + 1)))));
      (v_LET_NON_REC_21210_n__3_p0_o.dims[0] = ((v_GENERATOR_21217_n__0_COUNT - 1) + 1));
      (v_LET_NON_REC_21210_n__3_p0_o.lower_bound[0] = 1);
      int32_t __g_21215 = 0;
      (v_GENERATOR_21217_n__2___forall_lb_2_0 = 1);
      (v_GENERATOR_21217_n__2___forall_ub_2_0 = v_GENERATOR_21217_n__0_COUNT);
      for ((v_GENERATOR_21217_n__2_I = 1); (v_GENERATOR_21217_n__2_I <= v_GENERATOR_21217_n__0_COUNT); (v_GENERATOR_21217_n__2_I++)) {
        (v_BODY_21218_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_21215_n__0_COUNT));
        (v_BODY_21218_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_21217_n__2_I));
        (v_BODY_21218_n__0_SCALE = SISAL_CAST(double, v_FORALL_21215_n__0_SCALE));
        (v_BODY_21218_n__0_START = SISAL_CAST(int32_t, v_FORALL_21215_n__0_START));
        (v_BODY_21218_n__0_UC = SISAL_CAST(sisal_array_t, v_FORALL_21215_n__0_UC));
        (v_BODY_21218_n__0_X = SISAL_CAST(sisal_array_t, v_FORALL_21215_n__0_X));
        (v_BODY_21218_n__0_Y = SISAL_CAST(sisal_array_t, v_FORALL_21215_n__0_Y));
        (v_BODY_21218_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_21217_n__2___forall_lb_2_0));
        (v_BODY_21218_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_21217_n__2___forall_ub_2_0));
        int32_t v_BODY_21218_n__1_p0_o = 0;
        (v_BODY_21218_n__1_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_21218_n__0_I) + SISAL_CAST(int32_t, v_BODY_21218_n__0_START))));
        int32_t v_BODY_21218_n__2_p0_o = 0;
        (v_BODY_21218_n__2_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_21218_n__3_p0_o = 0;
        (v_BODY_21218_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_21218_n__1_p0_o) - SISAL_CAST(int32_t, v_BODY_21218_n__2_p0_o))));
        double v_BODY_21218_n__4_p0_o = 0;
        (v_BODY_21218_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_21218_n__0_X).data)[(SISAL_CAST(int32_t, v_BODY_21218_n__3_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_21218_n__0_X).lower_bound[0])]));
        double v_BODY_21218_n__5_p0_o = 0;
        (v_BODY_21218_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_21218_n__0_SCALE) * SISAL_CAST(double, v_BODY_21218_n__4_p0_o))));
        int32_t v_BODY_21218_n__6_p0_o = 0;
        (v_BODY_21218_n__6_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_21218_n__0_I) + SISAL_CAST(int32_t, v_BODY_21218_n__0_START))));
        int32_t v_BODY_21218_n__7_p0_o = 0;
        (v_BODY_21218_n__7_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_21218_n__8_p0_o = 0;
        (v_BODY_21218_n__8_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_21218_n__6_p0_o) - SISAL_CAST(int32_t, v_BODY_21218_n__7_p0_o))));
        double v_BODY_21218_n__9_p0_o = 0;
        (v_BODY_21218_n__9_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_21218_n__0_Y).data)[(SISAL_CAST(int32_t, v_BODY_21218_n__8_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_21218_n__0_Y).lower_bound[0])]));
        double v_BODY_21218_n__10_p0_o = 0;
        (v_BODY_21218_n__10_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_21218_n__5_p0_o) + SISAL_CAST(double, v_BODY_21218_n__9_p0_o))));
        (((double *)v_LET_NON_REC_21210_n__3_p0_o.data)[__g_21215] = SISAL_CAST(double, v_BODY_21218_n__10_p0_o));
        (__g_21215++);
      }
    }
    sisal_array_t v_LET_NON_REC_21210_n__5_p0_o = {0};
    (v_LET_NON_REC_21210_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_addh_arr(SISAL_CAST(sisal_array_t, v_LET_NON_REC_21210_n__1_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_21210_n__3_p0_o))));
    (v_g5_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_21210_n__5_p0_o));
  }
  (v_g5_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g5_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g5_n__0_p0_i);
}

extern "C" double func_SDOT(int32_t START, int32_t COUNT, sisal_array_t SX, sisal_array_t SY) {
  int32_t v_g6_n__0_COUNT = 0;
  int32_t v_g6_n__0_START = 0;
  sisal_array_t v_g6_n__0_SX = {0};
  sisal_array_t v_g6_n__0_SY = {0};
  (v_g6_n__0_START = SISAL_CAST(int32_t, START));
  (v_g6_n__0_COUNT = SISAL_CAST(int32_t, COUNT));
  (v_g6_n__0_SX = SISAL_CAST(sisal_array_t, SX));
  (v_g6_n__0_SY = SISAL_CAST(sisal_array_t, SY));
  double v_g6_n__0_p0_i = 0;
  double v_g6_n__1_p0_o = 0;
  {
    int32_t v_FORALL_20206_n__0_COUNT = v_g6_n__0_COUNT;
    int32_t v_FORALL_20206_n__2_I;
    int32_t v_FORALL_20206_n__0_START = v_g6_n__0_START;
    sisal_array_t v_FORALL_20206_n__0_SX = v_g6_n__0_SX;
    sisal_array_t v_FORALL_20206_n__0_SY = v_g6_n__0_SY;
    double v_FORALL_20206_n__3___forall_body_0;
    int32_t v_FORALL_20206_n__2___forall_lb_2_0;
    int32_t v_FORALL_20206_n__2___forall_ub_2_0;
    int32_t v_GENERATOR_20208_n__0_COUNT;
    int32_t v_GENERATOR_20208_n__2_I;
    int32_t v_GENERATOR_20208_n__0_START;
    sisal_array_t v_GENERATOR_20208_n__0_SX;
    sisal_array_t v_GENERATOR_20208_n__0_SY;
    int32_t v_GENERATOR_20208_n__2___forall_lb_2_0;
    int32_t v_GENERATOR_20208_n__2___forall_ub_2_0;
    int32_t v_BODY_20209_n__0_COUNT;
    int32_t v_BODY_20209_n__0_I;
    int32_t v_BODY_20209_n__0_START;
    sisal_array_t v_BODY_20209_n__0_SX;
    sisal_array_t v_BODY_20209_n__0_SY;
    int32_t v_BODY_20209_n__0___forall_lb_2_0;
    int32_t v_BODY_20209_n__0___forall_ub_2_0;
    (v_GENERATOR_20208_n__0_COUNT = v_FORALL_20206_n__0_COUNT);
    (v_g6_n__1_p0_o = 0);
    (v_GENERATOR_20208_n__2___forall_lb_2_0 = 1);
    (v_GENERATOR_20208_n__2___forall_ub_2_0 = v_GENERATOR_20208_n__0_COUNT);
    for ((v_GENERATOR_20208_n__2_I = 1); (v_GENERATOR_20208_n__2_I <= v_GENERATOR_20208_n__0_COUNT); (v_GENERATOR_20208_n__2_I++)) {
      (v_BODY_20209_n__0_COUNT = SISAL_CAST(int32_t, v_FORALL_20206_n__0_COUNT));
      (v_BODY_20209_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_20208_n__2_I));
      (v_BODY_20209_n__0_START = SISAL_CAST(int32_t, v_FORALL_20206_n__0_START));
      (v_BODY_20209_n__0_SX = SISAL_CAST(sisal_array_t, v_FORALL_20206_n__0_SX));
      (v_BODY_20209_n__0_SY = SISAL_CAST(sisal_array_t, v_FORALL_20206_n__0_SY));
      (v_BODY_20209_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_20208_n__2___forall_lb_2_0));
      (v_BODY_20209_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_20208_n__2___forall_ub_2_0));
      int32_t v_BODY_20209_n__1_p0_o = 0;
      (v_BODY_20209_n__1_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_20209_n__0_I) + SISAL_CAST(int32_t, v_BODY_20209_n__0_START))));
      int32_t v_BODY_20209_n__2_p0_o = 0;
      (v_BODY_20209_n__2_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_BODY_20209_n__3_p0_o = 0;
      (v_BODY_20209_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_20209_n__1_p0_o) - SISAL_CAST(int32_t, v_BODY_20209_n__2_p0_o))));
      double v_BODY_20209_n__4_p0_o = 0;
      (v_BODY_20209_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_20209_n__0_SX).data)[(SISAL_CAST(int32_t, v_BODY_20209_n__3_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_20209_n__0_SX).lower_bound[0])]));
      int32_t v_BODY_20209_n__5_p0_o = 0;
      (v_BODY_20209_n__5_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_20209_n__0_I) + SISAL_CAST(int32_t, v_BODY_20209_n__0_START))));
      int32_t v_BODY_20209_n__6_p0_o = 0;
      (v_BODY_20209_n__6_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_BODY_20209_n__7_p0_o = 0;
      (v_BODY_20209_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_20209_n__5_p0_o) - SISAL_CAST(int32_t, v_BODY_20209_n__6_p0_o))));
      double v_BODY_20209_n__8_p0_o = 0;
      (v_BODY_20209_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_20209_n__0_SY).data)[(SISAL_CAST(int32_t, v_BODY_20209_n__7_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_20209_n__0_SY).lower_bound[0])]));
      double v_BODY_20209_n__9_p0_o = 0;
      (v_BODY_20209_n__9_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_20209_n__4_p0_o) * SISAL_CAST(double, v_BODY_20209_n__8_p0_o))));
      (v_g6_n__1_p0_o = (v_g6_n__1_p0_o + SISAL_CAST(double, v_BODY_20209_n__9_p0_o)));
    }
  }
  (v_g6_n__0_p0_i = SISAL_CAST(double, v_g6_n__1_p0_o));
  return SISAL_CAST(double, v_g6_n__0_p0_i);
}

extern "C" sisal_array_t func_CALC_Z3(sisal_array_t A, sisal_array_t Z_IN, sisal_array_t IPVT, int32_t N) {
  sisal_array_t v_g7_n__0_A = {0};
  sisal_array_t v_g7_n__0_IPVT = {0};
  int32_t v_g7_n__0_N = 0;
  sisal_array_t v_g7_n__0_Z_IN = {0};
  (v_g7_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g7_n__0_Z_IN = SISAL_CAST(sisal_array_t, Z_IN));
  (v_g7_n__0_IPVT = SISAL_CAST(sisal_array_t, IPVT));
  (v_g7_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g7_n__0_p0_i = {0};
  sisal_array_t v_g7_n__1_p0_o = {0};
  {
    int32_t v_LoopB_19189_n__5_MERGE_KB = 0;
    sisal_array_t v_LoopB_19189_n__6_MERGE_Z = {0};
    int32_t v_LoopB_19189_n__7_MERGE_OLD_KB = 0;
    sisal_array_t v_LoopB_19189_n__8_MERGE_OLD_Z = {0};
    bool v_LoopB_19189_n__9_MERGE_first = 0;
    int32_t v_LoopB_19189_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_19189_bodycap_n8_p0 = {0};
    bool v_LoopB_19189_bodycap_n10_p0 = 0;
    sisal_array_t v_LoopB_19189_n__0_A = {0};
    (v_LoopB_19189_n__0_A = SISAL_CAST(sisal_array_t, v_g7_n__0_A));
    sisal_array_t v_LoopB_19189_n__0_IPVT = {0};
    (v_LoopB_19189_n__0_IPVT = SISAL_CAST(sisal_array_t, v_g7_n__0_IPVT));
    int32_t v_LoopB_19189_n__0_N = 0;
    (v_LoopB_19189_n__0_N = SISAL_CAST(int32_t, v_g7_n__0_N));
    sisal_array_t v_LoopB_19189_n__0_Z_IN = {0};
    (v_LoopB_19189_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_g7_n__0_Z_IN));
    sisal_array_t v_INIT_19205_n__0_A = {0};
    sisal_array_t v_INIT_19205_n__0_IPVT = {0};
    int32_t v_INIT_19205_n__1_KB = 0;
    int32_t v_INIT_19205_n__0_N = 0;
    int32_t v_INIT_19205_n__1_OLD_KB = 0;
    sisal_array_t v_INIT_19205_n__0_OLD_Z = {0};
    sisal_array_t v_INIT_19205_n__0_Z = {0};
    sisal_array_t v_INIT_19205_n__0_Z_IN = {0};
    (v_INIT_19205_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_A));
    (v_INIT_19205_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_IPVT));
    (v_INIT_19205_n__0_N = SISAL_CAST(int32_t, v_LoopB_19189_n__0_N));
    (v_INIT_19205_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_Z_IN));
    (v_INIT_19205_n__1_OLD_KB = SISAL_CAST(int32_t, 1));
    bool v_INIT_19205_n__2_p0_o = 0;
    (v_INIT_19205_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_19189_n__5_MERGE_KB = v_INIT_19205_n__1_OLD_KB);
    (v_LoopB_19189_n__6_MERGE_Z = v_INIT_19205_n__0_Z_IN);
    (v_LoopB_19189_n__7_MERGE_OLD_KB = v_INIT_19205_n__1_OLD_KB);
    (v_LoopB_19189_n__8_MERGE_OLD_Z = v_INIT_19205_n__0_Z_IN);
    (v_LoopB_19189_n__9_MERGE_first = v_INIT_19205_n__2_p0_o);
    sisal_array_t v_TEST_19204_n__0_A = {0};
    sisal_array_t v_TEST_19204_n__0_IPVT = {0};
    int32_t v_TEST_19204_n__0_KB = 0;
    int32_t v_TEST_19204_n__0_N = 0;
    int32_t v_TEST_19204_n__0_OLD_KB = 0;
    sisal_array_t v_TEST_19204_n__0_OLD_Z = {0};
    sisal_array_t v_TEST_19204_n__0_Z = {0};
    sisal_array_t v_TEST_19204_n__0_Z_IN = {0};
    (v_TEST_19204_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_A));
    (v_TEST_19204_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_IPVT));
    (v_TEST_19204_n__0_KB = SISAL_CAST(int32_t, v_LoopB_19189_n__5_MERGE_KB));
    (v_TEST_19204_n__0_N = SISAL_CAST(int32_t, v_LoopB_19189_n__0_N));
    (v_TEST_19204_n__0_OLD_KB = SISAL_CAST(int32_t, v_LoopB_19189_n__7_MERGE_OLD_KB));
    (v_TEST_19204_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__8_MERGE_OLD_Z));
    (v_TEST_19204_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__6_MERGE_Z));
    (v_TEST_19204_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_Z_IN));
    bool v_TEST_19204_n__1_p0_o = 0;
    (v_TEST_19204_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_19204_n__0_KB) <= SISAL_CAST(int32_t, v_TEST_19204_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_19204_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_19189 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_19204_n__1_p0_o) {
      sisal_array_t v_BODY_19190_n__0_A = {0};
      sisal_array_t v_BODY_19190_n__0_IPVT = {0};
      int32_t v_BODY_19190_n__5_K = 0;
      int32_t v_BODY_19190_n__2_KB = 0;
      int32_t v_BODY_19190_n__0_N = 0;
      int32_t v_BODY_19190_n__0_OLD_KB = 0;
      sisal_array_t v_BODY_19190_n__0_OLD_Z = {0};
      sisal_array_t v_BODY_19190_n__8_Z = {0};
      sisal_array_t v_BODY_19190_n__6_Z2 = {0};
      sisal_array_t v_BODY_19190_n__0_Z_IN = {0};
      sisal_array_t v_BODY_19190_n__0_p6_o = {0};
      (v_BODY_19190_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_A));
      (v_BODY_19190_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_IPVT));
      int32_t v_BODY_19190_n__0_p2_o = 0;
      (v_BODY_19190_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_19189_n__5_MERGE_KB));
      (v_BODY_19190_n__0_N = SISAL_CAST(int32_t, v_LoopB_19189_n__0_N));
      (v_BODY_19190_n__0_OLD_KB = SISAL_CAST(int32_t, v_LoopB_19189_n__7_MERGE_OLD_KB));
      (v_BODY_19190_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__8_MERGE_OLD_Z));
      (v_BODY_19190_n__0_p6_o = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__6_MERGE_Z));
      (v_BODY_19190_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_Z_IN));
      int32_t v_BODY_19190_n__1_p0_o = 0;
      (v_BODY_19190_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_19190_n__2_KB = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_19190_n__0_OLD_KB) + SISAL_CAST(int32_t, v_BODY_19190_n__1_p0_o))));
      int32_t v_BODY_19190_n__3_p0_o = 0;
      (v_BODY_19190_n__3_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_BODY_19190_n__4_p0_o = 0;
      (v_BODY_19190_n__4_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_19190_n__0_N) + SISAL_CAST(int32_t, v_BODY_19190_n__3_p0_o))));
      (v_BODY_19190_n__5_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_19190_n__4_p0_o) - SISAL_CAST(int32_t, v_BODY_19190_n__0_OLD_KB))));
      int32_t v_IF_array_dv_DOUBLE____19191_n__0_K = 0;
      (v_IF_array_dv_DOUBLE____19191_n__0_K = SISAL_CAST(int32_t, v_BODY_19190_n__5_K));
      int32_t v_IF_array_dv_DOUBLE____19191_n__0_N = 0;
      (v_IF_array_dv_DOUBLE____19191_n__0_N = SISAL_CAST(int32_t, v_BODY_19190_n__0_N));
      sisal_array_t v_IF_array_dv_DOUBLE____19191_n__0_OLD_Z = {0};
      (v_IF_array_dv_DOUBLE____19191_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_OLD_Z));
      sisal_array_t v_IF_array_dv_DOUBLE____19191_n__0_A = {0};
      (v_IF_array_dv_DOUBLE____19191_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_A));
      sisal_array_t v_IF_array_dv_DOUBLE____19191_n__0_IPVT = {0};
      (v_IF_array_dv_DOUBLE____19191_n__0_IPVT = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_IPVT));
      int32_t v_IF_array_dv_DOUBLE____19191_n__0_KB = 0;
      (v_IF_array_dv_DOUBLE____19191_n__0_KB = SISAL_CAST(int32_t, v_BODY_19190_n__2_KB));
      int32_t v_IF_array_dv_DOUBLE____19191_n__0_OLD_KB = 0;
      (v_IF_array_dv_DOUBLE____19191_n__0_OLD_KB = SISAL_CAST(int32_t, v_BODY_19190_n__0_OLD_KB));
      sisal_array_t v_IF_array_dv_DOUBLE____19191_n__0_Z = {0};
      (v_IF_array_dv_DOUBLE____19191_n__0_Z = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_p6_o));
      sisal_array_t v_IF_array_dv_DOUBLE____19191_n__0_Z_IN = {0};
      (v_IF_array_dv_DOUBLE____19191_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_Z_IN));
      {
        int32_t v_PREDICATE_19192_n__0_K = 0;
        int32_t v_PREDICATE_19192_n__0_N = 0;
        (v_PREDICATE_19192_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19191_n__0_K));
        (v_PREDICATE_19192_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19191_n__0_N));
        bool v_PREDICATE_19192_n__1_p0_o = 0;
        (v_PREDICATE_19192_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_19192_n__0_K) < SISAL_CAST(int32_t, v_PREDICATE_19192_n__0_N))));
        if (v_PREDICATE_19192_n__1_p0_o) {
          sisal_array_t v_THEN_19194_n__0_A = {0};
          sisal_array_t v_THEN_19194_n__0_IPVT = {0};
          int32_t v_THEN_19194_n__0_K = 0;
          int32_t v_THEN_19194_n__0_KB = 0;
          int32_t v_THEN_19194_n__0_N = 0;
          int32_t v_THEN_19194_n__0_OLD_KB = 0;
          sisal_array_t v_THEN_19194_n__0_OLD_Z = {0};
          sisal_array_t v_THEN_19194_n__0_Z = {0};
          sisal_array_t v_THEN_19194_n__0_Z_IN = {0};
          (v_THEN_19194_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19191_n__0_OLD_Z));
          (v_THEN_19194_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19191_n__0_K));
          (v_THEN_19194_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19191_n__0_N));
          (v_THEN_19194_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19191_n__0_A));
          (v_THEN_19194_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19191_n__0_IPVT));
          (v_THEN_19194_n__0_KB = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19191_n__0_KB));
          (v_THEN_19194_n__0_OLD_KB = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19191_n__0_OLD_KB));
          (v_THEN_19194_n__0_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19191_n__0_Z));
          (v_THEN_19194_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19191_n__0_Z_IN));
          double v_THEN_19194_n__1_p0_o = 0;
          (v_THEN_19194_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_THEN_19194_n__0_K) - SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_OLD_Z).lower_bound[0])]));
          int32_t v_THEN_19194_n__2_p0_o = 0;
          (v_THEN_19194_n__2_p0_o = SISAL_CAST(int32_t, 1));
          float v_THEN_19194_n__3_p0_o = 0;
          (v_THEN_19194_n__3_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_THEN_19194_n__0_K) + SISAL_CAST(int32_t, v_THEN_19194_n__2_p0_o))));
          float v_THEN_19194_n__4_p0_o = 0;
          (v_THEN_19194_n__4_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_THEN_19194_n__0_N) - SISAL_CAST(int32_t, v_THEN_19194_n__0_K))));
          {
            sisal_array_t v_LET_NON_REC_19195_n__0_A = {0};
            sisal_array_t v_LET_NON_REC_19195_n__0_IPVT = {0};
            int32_t v_LET_NON_REC_19195_n__0_K = 0;
            int32_t v_LET_NON_REC_19195_n__0_KB = 0;
            int32_t v_LET_NON_REC_19195_n__0_N = 0;
            int32_t v_LET_NON_REC_19195_n__0_OLD_KB = 0;
            sisal_array_t v_LET_NON_REC_19195_n__0_OLD_Z = {0};
            sisal_array_t v_LET_NON_REC_19195_n__1_TRANS_A = {0};
            sisal_array_t v_LET_NON_REC_19195_n__0_Z = {0};
            sisal_array_t v_LET_NON_REC_19195_n__0_Z_IN = {0};
            (v_LET_NON_REC_19195_n__0_A = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_A));
            (v_LET_NON_REC_19195_n__0_IPVT = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_IPVT));
            (v_LET_NON_REC_19195_n__0_K = SISAL_CAST(int32_t, v_THEN_19194_n__0_K));
            (v_LET_NON_REC_19195_n__0_KB = SISAL_CAST(int32_t, v_THEN_19194_n__0_KB));
            (v_LET_NON_REC_19195_n__0_N = SISAL_CAST(int32_t, v_THEN_19194_n__0_N));
            (v_LET_NON_REC_19195_n__0_OLD_KB = SISAL_CAST(int32_t, v_THEN_19194_n__0_OLD_KB));
            (v_LET_NON_REC_19195_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_OLD_Z));
            (v_LET_NON_REC_19195_n__0_Z = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_Z));
            (v_LET_NON_REC_19195_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_Z_IN));
            (v_LET_NON_REC_19195_n__1_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19195_n__0_A))));
            sisal_array_t v_LET_NON_REC_19195_n__2_p0_o = {0};
            (v_LET_NON_REC_19195_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19195_n__1_TRANS_A), (SISAL_CAST(int32_t, v_LET_NON_REC_19195_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19195_n__1_TRANS_A).lower_bound[0]))));
          }
          int32_t v_THEN_19194_n__7_p0_o = 0;
          (v_THEN_19194_n__7_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_THEN_19194_n__8_p0_o = 0;
          (v_THEN_19194_n__8_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_THEN_19194_n__0_K) + SISAL_CAST(int32_t, v_THEN_19194_n__7_p0_o))));
          int32_t v_THEN_19194_n__9_p0_o = 0;
          (v_THEN_19194_n__9_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_THEN_19194_n__0_N) - SISAL_CAST(int32_t, v_THEN_19194_n__0_K))));
          sisal_array_t v_THEN_19194_n__10_p0_o = {0};
          {
            sisal_array_t v_LET_NON_REC_19196_n__0_A = {0};
            sisal_array_t v_LET_NON_REC_19196_n__0_IPVT = {0};
            int32_t v_LET_NON_REC_19196_n__0_K = 0;
            int32_t v_LET_NON_REC_19196_n__0_KB = 0;
            int32_t v_LET_NON_REC_19196_n__0_N = 0;
            int32_t v_LET_NON_REC_19196_n__0_OLD_KB = 0;
            sisal_array_t v_LET_NON_REC_19196_n__0_OLD_Z = {0};
            sisal_array_t v_LET_NON_REC_19196_n__1_TRANS_A = {0};
            sisal_array_t v_LET_NON_REC_19196_n__0_Z = {0};
            sisal_array_t v_LET_NON_REC_19196_n__0_Z_IN = {0};
            (v_LET_NON_REC_19196_n__0_A = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_A));
            (v_LET_NON_REC_19196_n__0_IPVT = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_IPVT));
            (v_LET_NON_REC_19196_n__0_K = SISAL_CAST(int32_t, v_THEN_19194_n__0_K));
            (v_LET_NON_REC_19196_n__0_KB = SISAL_CAST(int32_t, v_THEN_19194_n__0_KB));
            (v_LET_NON_REC_19196_n__0_N = SISAL_CAST(int32_t, v_THEN_19194_n__0_N));
            (v_LET_NON_REC_19196_n__0_OLD_KB = SISAL_CAST(int32_t, v_THEN_19194_n__0_OLD_KB));
            (v_LET_NON_REC_19196_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_OLD_Z));
            (v_LET_NON_REC_19196_n__0_Z = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_Z));
            (v_LET_NON_REC_19196_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_Z_IN));
            (v_LET_NON_REC_19196_n__1_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19196_n__0_A))));
            sisal_array_t v_LET_NON_REC_19196_n__2_p0_o = {0};
            (v_LET_NON_REC_19196_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19196_n__1_TRANS_A), (SISAL_CAST(int32_t, v_LET_NON_REC_19196_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19196_n__1_TRANS_A).lower_bound[0]))));
            (v_THEN_19194_n__10_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_19196_n__2_p0_o));
          }
          double v_THEN_19194_n__12_p0_o = 0;
          (v_THEN_19194_n__12_p0_o = SISAL_CAST(double, func_SDOT(SISAL_CAST(int32_t, v_THEN_19194_n__8_p0_o), SISAL_CAST(int32_t, v_THEN_19194_n__9_p0_o), SISAL_CAST(sisal_array_t, v_THEN_19194_n__10_p0_o), SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_OLD_Z))));
          double v_THEN_19194_n__13_p0_o = 0;
          (v_THEN_19194_n__13_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_19194_n__1_p0_o) + SISAL_CAST(double, v_THEN_19194_n__12_p0_o))));
          sisal_array_t v_THEN_19194_n__14_p0_o = {0};
          (v_THEN_19194_n__14_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_19194_n__0_OLD_Z), ((int64_t)SISAL_CAST(int32_t, v_THEN_19194_n__0_K)), SISAL_CAST(double, SISAL_CAST(double, v_THEN_19194_n__13_p0_o)))));
          (v_BODY_19190_n__6_Z2 = SISAL_CAST(sisal_array_t, v_THEN_19194_n__14_p0_o));
        }
        else {
          sisal_array_t v_ELSE_19193_n__0_OLD_Z = {0};
          (v_ELSE_19193_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19191_n__0_OLD_Z));
          (v_BODY_19190_n__6_Z2 = SISAL_CAST(sisal_array_t, v_ELSE_19193_n__0_OLD_Z));
        }
      }
      sisal_array_t v_IF_array_dv_DOUBLE____19197_n__0_Z2 = {0};
      (v_IF_array_dv_DOUBLE____19197_n__0_Z2 = SISAL_CAST(sisal_array_t, v_BODY_19190_n__6_Z2));
      int32_t v_IF_array_dv_DOUBLE____19197_n__0_K = 0;
      (v_IF_array_dv_DOUBLE____19197_n__0_K = SISAL_CAST(int32_t, v_BODY_19190_n__5_K));
      sisal_array_t v_IF_array_dv_DOUBLE____19197_n__0_A = {0};
      (v_IF_array_dv_DOUBLE____19197_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_A));
      sisal_array_t v_IF_array_dv_DOUBLE____19197_n__0_IPVT = {0};
      (v_IF_array_dv_DOUBLE____19197_n__0_IPVT = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_IPVT));
      int32_t v_IF_array_dv_DOUBLE____19197_n__0_KB = 0;
      (v_IF_array_dv_DOUBLE____19197_n__0_KB = SISAL_CAST(int32_t, v_BODY_19190_n__2_KB));
      int32_t v_IF_array_dv_DOUBLE____19197_n__0_N = 0;
      (v_IF_array_dv_DOUBLE____19197_n__0_N = SISAL_CAST(int32_t, v_BODY_19190_n__0_N));
      int32_t v_IF_array_dv_DOUBLE____19197_n__0_OLD_KB = 0;
      (v_IF_array_dv_DOUBLE____19197_n__0_OLD_KB = SISAL_CAST(int32_t, v_BODY_19190_n__0_OLD_KB));
      sisal_array_t v_IF_array_dv_DOUBLE____19197_n__0_OLD_Z = {0};
      (v_IF_array_dv_DOUBLE____19197_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_OLD_Z));
      sisal_array_t v_IF_array_dv_DOUBLE____19197_n__0_Z = {0};
      (v_IF_array_dv_DOUBLE____19197_n__0_Z = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_p6_o));
      sisal_array_t v_IF_array_dv_DOUBLE____19197_n__0_Z_IN = {0};
      (v_IF_array_dv_DOUBLE____19197_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_BODY_19190_n__0_Z_IN));
      {
        int32_t v_PREDICATE_19198_n__0_K = 0;
        sisal_array_t v_PREDICATE_19198_n__0_Z2 = {0};
        (v_PREDICATE_19198_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z2));
        (v_PREDICATE_19198_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_K));
        float v_PREDICATE_19198_n__1_p0_o = 0;
        (v_PREDICATE_19198_n__1_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_PREDICATE_19198_n__0_Z2).data)[(SISAL_CAST(int32_t, v_PREDICATE_19198_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_19198_n__0_Z2).lower_bound[0])]));
        double v_PREDICATE_19198_n__2_p0_o = 0;
        (v_PREDICATE_19198_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_19198_n__0_Z2).data)[(SISAL_CAST(int32_t, v_PREDICATE_19198_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_19198_n__0_Z2).lower_bound[0])]));
        double v_PREDICATE_19198_n__3_p0_o = 0;
        (v_PREDICATE_19198_n__3_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_19198_n__2_p0_o))));
        double v_PREDICATE_19198_n__4_p0_o = 0;
        (v_PREDICATE_19198_n__4_p0_o = SISAL_CAST(double, 1.));
        bool v_PREDICATE_19198_n__5_p0_o = 0;
        (v_PREDICATE_19198_n__5_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_19198_n__3_p0_o) <= SISAL_CAST(double, v_PREDICATE_19198_n__4_p0_o))));
        if (v_PREDICATE_19198_n__5_p0_o) {
          sisal_array_t v_THEN_19201_n__0_A = {0};
          sisal_array_t v_THEN_19201_n__0_IPVT = {0};
          int32_t v_THEN_19201_n__0_K = 0;
          int32_t v_THEN_19201_n__0_KB = 0;
          int32_t v_THEN_19201_n__0_N = 0;
          int32_t v_THEN_19201_n__0_OLD_KB = 0;
          sisal_array_t v_THEN_19201_n__0_OLD_Z = {0};
          sisal_array_t v_THEN_19201_n__0_Z = {0};
          sisal_array_t v_THEN_19201_n__0_Z2 = {0};
          sisal_array_t v_THEN_19201_n__0_Z_IN = {0};
          (v_THEN_19201_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_A));
          (v_THEN_19201_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_IPVT));
          (v_THEN_19201_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_K));
          (v_THEN_19201_n__0_KB = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_KB));
          (v_THEN_19201_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_N));
          (v_THEN_19201_n__0_OLD_KB = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_OLD_KB));
          (v_THEN_19201_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_OLD_Z));
          (v_THEN_19201_n__0_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z));
          (v_THEN_19201_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z2));
          (v_THEN_19201_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z_IN));
          sisal_array_t v_THEN_19201_n__1_p0_o = {0};
          {
            sisal_array_t v_LET_NON_REC_19202_n__0_A = {0};
            sisal_array_t v_LET_NON_REC_19202_n__0_IPVT = {0};
            int32_t v_LET_NON_REC_19202_n__0_K = 0;
            int32_t v_LET_NON_REC_19202_n__0_KB = 0;
            int32_t v_LET_NON_REC_19202_n__1_L = 0;
            int32_t v_LET_NON_REC_19202_n__0_N = 0;
            int32_t v_LET_NON_REC_19202_n__0_OLD_KB = 0;
            sisal_array_t v_LET_NON_REC_19202_n__0_OLD_Z = {0};
            sisal_array_t v_LET_NON_REC_19202_n__0_Z = {0};
            sisal_array_t v_LET_NON_REC_19202_n__0_Z2 = {0};
            sisal_array_t v_LET_NON_REC_19202_n__0_Z_IN = {0};
            (v_LET_NON_REC_19202_n__0_A = SISAL_CAST(sisal_array_t, v_THEN_19201_n__0_A));
            (v_LET_NON_REC_19202_n__0_IPVT = SISAL_CAST(sisal_array_t, v_THEN_19201_n__0_IPVT));
            (v_LET_NON_REC_19202_n__0_K = SISAL_CAST(int32_t, v_THEN_19201_n__0_K));
            (v_LET_NON_REC_19202_n__0_KB = SISAL_CAST(int32_t, v_THEN_19201_n__0_KB));
            (v_LET_NON_REC_19202_n__0_N = SISAL_CAST(int32_t, v_THEN_19201_n__0_N));
            (v_LET_NON_REC_19202_n__0_OLD_KB = SISAL_CAST(int32_t, v_THEN_19201_n__0_OLD_KB));
            (v_LET_NON_REC_19202_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_THEN_19201_n__0_OLD_Z));
            (v_LET_NON_REC_19202_n__0_Z = SISAL_CAST(sisal_array_t, v_THEN_19201_n__0_Z));
            (v_LET_NON_REC_19202_n__0_Z2 = SISAL_CAST(sisal_array_t, v_THEN_19201_n__0_Z2));
            (v_LET_NON_REC_19202_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_THEN_19201_n__0_Z_IN));
            (v_LET_NON_REC_19202_n__1_L = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_IPVT).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19202_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_IPVT).lower_bound[0])]));
            double v_LET_NON_REC_19202_n__2_p0_o = 0;
            (v_LET_NON_REC_19202_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19202_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_Z2).lower_bound[0])]));
            sisal_array_t v_LET_NON_REC_19202_n__3_p0_o = {0};
            (v_LET_NON_REC_19202_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_Z2), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_19202_n__1_L)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_19202_n__2_p0_o)))));
            double v_LET_NON_REC_19202_n__4_p0_o = 0;
            (v_LET_NON_REC_19202_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19202_n__1_L) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__0_Z2).lower_bound[0])]));
            sisal_array_t v_LET_NON_REC_19202_n__5_p0_o = {0};
            (v_LET_NON_REC_19202_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__3_p0_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_19202_n__0_K)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_19202_n__4_p0_o)))));
            (v_THEN_19201_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_19202_n__5_p0_o));
          }
          (v_BODY_19190_n__8_Z = SISAL_CAST(sisal_array_t, v_THEN_19201_n__1_p0_o));
        }
        else {
          sisal_array_t v_ELSE_19199_n__0_A = {0};
          sisal_array_t v_ELSE_19199_n__0_IPVT = {0};
          int32_t v_ELSE_19199_n__0_K = 0;
          int32_t v_ELSE_19199_n__0_KB = 0;
          int32_t v_ELSE_19199_n__0_N = 0;
          int32_t v_ELSE_19199_n__0_OLD_KB = 0;
          sisal_array_t v_ELSE_19199_n__0_OLD_Z = {0};
          sisal_array_t v_ELSE_19199_n__0_Z = {0};
          sisal_array_t v_ELSE_19199_n__0_Z2 = {0};
          sisal_array_t v_ELSE_19199_n__0_Z_IN = {0};
          (v_ELSE_19199_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_A));
          (v_ELSE_19199_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_IPVT));
          (v_ELSE_19199_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_K));
          (v_ELSE_19199_n__0_KB = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_KB));
          (v_ELSE_19199_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_N));
          (v_ELSE_19199_n__0_OLD_KB = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____19197_n__0_OLD_KB));
          (v_ELSE_19199_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_OLD_Z));
          (v_ELSE_19199_n__0_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z));
          (v_ELSE_19199_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z2));
          (v_ELSE_19199_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____19197_n__0_Z_IN));
          sisal_array_t v_ELSE_19199_n__1_p0_o = {0};
          {
            sisal_array_t v_LET_NON_REC_19200_n__0_A = {0};
            sisal_array_t v_LET_NON_REC_19200_n__0_IPVT = {0};
            int32_t v_LET_NON_REC_19200_n__0_K = 0;
            int32_t v_LET_NON_REC_19200_n__0_KB = 0;
            int32_t v_LET_NON_REC_19200_n__16_L = 0;
            int32_t v_LET_NON_REC_19200_n__0_N = 0;
            int32_t v_LET_NON_REC_19200_n__0_OLD_KB = 0;
            sisal_array_t v_LET_NON_REC_19200_n__0_OLD_Z = {0};
            sisal_array_t v_LET_NON_REC_19200_n__0_Z = {0};
            sisal_array_t v_LET_NON_REC_19200_n__0_Z2 = {0};
            sisal_array_t v_LET_NON_REC_19200_n__15_Z4 = {0};
            sisal_array_t v_LET_NON_REC_19200_n__0_Z_IN = {0};
            (v_LET_NON_REC_19200_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__0_A));
            (v_LET_NON_REC_19200_n__0_IPVT = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__0_IPVT));
            (v_LET_NON_REC_19200_n__0_K = SISAL_CAST(int32_t, v_ELSE_19199_n__0_K));
            (v_LET_NON_REC_19200_n__0_KB = SISAL_CAST(int32_t, v_ELSE_19199_n__0_KB));
            (v_LET_NON_REC_19200_n__0_N = SISAL_CAST(int32_t, v_ELSE_19199_n__0_N));
            (v_LET_NON_REC_19200_n__0_OLD_KB = SISAL_CAST(int32_t, v_ELSE_19199_n__0_OLD_KB));
            (v_LET_NON_REC_19200_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__0_OLD_Z));
            (v_LET_NON_REC_19200_n__0_Z = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__0_Z));
            (v_LET_NON_REC_19200_n__0_Z2 = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__0_Z2));
            (v_LET_NON_REC_19200_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__0_Z_IN));
            int32_t v_LET_NON_REC_19200_n__1_p0_o = 0;
            (v_LET_NON_REC_19200_n__1_p0_o = SISAL_CAST(int32_t, 1));
            double v_LET_NON_REC_19200_n__2_p0_o = 0;
            (v_LET_NON_REC_19200_n__2_p0_o = SISAL_CAST(double, 1.));
            double v_LET_NON_REC_19200_n__3_p0_o = 0;
            (v_LET_NON_REC_19200_n__3_p0_o = SISAL_CAST(double, 1.));
            float v_LET_NON_REC_19200_n__4_p0_o = 0;
            (v_LET_NON_REC_19200_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).lower_bound[0])]));
            double v_LET_NON_REC_19200_n__5_p0_o = 0;
            (v_LET_NON_REC_19200_n__5_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).lower_bound[0])]));
            double v_LET_NON_REC_19200_n__6_p0_o = 0;
            (v_LET_NON_REC_19200_n__6_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_19200_n__5_p0_o))));
            float v_LET_NON_REC_19200_n__7_p0_o = 0;
            (v_LET_NON_REC_19200_n__7_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_LET_NON_REC_19200_n__3_p0_o) / SISAL_CAST(double, v_LET_NON_REC_19200_n__6_p0_o))));
            int32_t v_LET_NON_REC_19200_n__8_p0_o = 0;
            (v_LET_NON_REC_19200_n__8_p0_o = SISAL_CAST(int32_t, 1));
            double v_LET_NON_REC_19200_n__9_p0_o = 0;
            (v_LET_NON_REC_19200_n__9_p0_o = SISAL_CAST(double, 1.));
            double v_LET_NON_REC_19200_n__10_p0_o = 0;
            (v_LET_NON_REC_19200_n__10_p0_o = SISAL_CAST(double, 1.));
            float v_LET_NON_REC_19200_n__11_p0_o = 0;
            (v_LET_NON_REC_19200_n__11_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).lower_bound[0])]));
            double v_LET_NON_REC_19200_n__12_p0_o = 0;
            (v_LET_NON_REC_19200_n__12_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2).lower_bound[0])]));
            double v_LET_NON_REC_19200_n__13_p0_o = 0;
            (v_LET_NON_REC_19200_n__13_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_19200_n__12_p0_o))));
            double v_LET_NON_REC_19200_n__14_p0_o = 0;
            (v_LET_NON_REC_19200_n__14_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_19200_n__10_p0_o) / SISAL_CAST(double, v_LET_NON_REC_19200_n__13_p0_o))));
            (v_LET_NON_REC_19200_n__15_Z4 = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__8_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_Z2), SISAL_CAST(double, v_LET_NON_REC_19200_n__14_p0_o))));
            (v_LET_NON_REC_19200_n__16_L = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_IPVT).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__0_IPVT).lower_bound[0])]));
            double v_LET_NON_REC_19200_n__17_p0_o = 0;
            (v_LET_NON_REC_19200_n__17_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__15_Z4).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__15_Z4).lower_bound[0])]));
            sisal_array_t v_LET_NON_REC_19200_n__18_p0_o = {0};
            (v_LET_NON_REC_19200_n__18_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__15_Z4), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__16_L)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_19200_n__17_p0_o)))));
            double v_LET_NON_REC_19200_n__19_p0_o = 0;
            (v_LET_NON_REC_19200_n__19_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__15_Z4).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__16_L) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__15_Z4).lower_bound[0])]));
            sisal_array_t v_LET_NON_REC_19200_n__20_p0_o = {0};
            (v_LET_NON_REC_19200_n__20_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__18_p0_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_19200_n__0_K)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_19200_n__19_p0_o)))));
            (v_ELSE_19199_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_19200_n__20_p0_o));
          }
          (v_BODY_19190_n__8_Z = SISAL_CAST(sisal_array_t, v_ELSE_19199_n__1_p0_o));
        }
      }
      bool v_BODY_19190_n__10_p0_o = 0;
      (v_BODY_19190_n__10_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_19189_bodycap_n2_p0 = v_BODY_19190_n__2_KB);
      (v_LoopB_19189_bodycap_n8_p0 = v_BODY_19190_n__8_Z);
      (v_LoopB_19189_bodycap_n10_p0 = v_BODY_19190_n__10_p0_o);
      (v_LoopB_19189_n__5_MERGE_KB = v_LoopB_19189_bodycap_n2_p0);
      (v_LoopB_19189_n__6_MERGE_Z = v_LoopB_19189_bodycap_n8_p0);
      (v_LoopB_19189_n__7_MERGE_OLD_KB = v_LoopB_19189_bodycap_n2_p0);
      (v_LoopB_19189_n__8_MERGE_OLD_Z = v_LoopB_19189_bodycap_n8_p0);
      (v_LoopB_19189_n__9_MERGE_first = v_LoopB_19189_bodycap_n10_p0);
      (v_TEST_19204_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_A));
      (v_TEST_19204_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_IPVT));
      (v_TEST_19204_n__0_KB = SISAL_CAST(int32_t, v_LoopB_19189_n__5_MERGE_KB));
      (v_TEST_19204_n__0_N = SISAL_CAST(int32_t, v_LoopB_19189_n__0_N));
      (v_TEST_19204_n__0_OLD_KB = SISAL_CAST(int32_t, v_LoopB_19189_n__7_MERGE_OLD_KB));
      (v_TEST_19204_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__8_MERGE_OLD_Z));
      (v_TEST_19204_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__6_MERGE_Z));
      (v_TEST_19204_n__0_Z_IN = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__0_Z_IN));
      (v_TEST_19204_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_19204_n__0_KB) <= SISAL_CAST(int32_t, v_TEST_19204_n__0_N))));
    }
    sisal_array_t v_RETURNS_19203_n__0_p0_o = {0};
    (v_RETURNS_19203_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_19189_n__8_MERGE_OLD_Z));
    sisal_array_t v_RETURNS_19203_n__1_p0_o = {0};
    (v_RETURNS_19203_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_19203_n__0_p0_o)));
    (v_g7_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_19203_n__1_p0_o));
  }
  (v_g7_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g7_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g7_n__0_p0_i);
}

extern "C" sisal_array_t func_CALC_Z1(sisal_array_t A, int32_t N) {
  sisal_array_t v_g8_n__0_A = {0};
  int32_t v_g8_n__0_N = 0;
  (v_g8_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g8_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g8_n__0_p0_i = {0};
  sisal_array_t v_g8_n__1_p0_o = {0};
  {
    sisal_array_t v_LET_NON_REC_18135_n__0_A = {0};
    int32_t v_LET_NON_REC_18135_n__0_N = 0;
    sisal_array_t v_LET_NON_REC_18135_n__2_Z1 = {0};
    (v_LET_NON_REC_18135_n__0_A = SISAL_CAST(sisal_array_t, v_g8_n__0_A));
    (v_LET_NON_REC_18135_n__0_N = SISAL_CAST(int32_t, v_g8_n__0_N));
    sisal_array_t v_LET_NON_REC_18135_n__1_p0_o = {0};
    {
      double v_LoopB_18136_n__5_MERGE_EK = 0;
      int32_t v_LoopB_18136_n__6_MERGE_K = 0;
      sisal_array_t v_LoopB_18136_n__7_MERGE_Z = {0};
      double v_LoopB_18136_n__8_MERGE_OLD_EK = 0;
      int32_t v_LoopB_18136_n__9_MERGE_OLD_K = 0;
      sisal_array_t v_LoopB_18136_n__10_MERGE_OLD_Z = {0};
      bool v_LoopB_18136_n__11_MERGE_first = 0;
      int32_t v_LoopB_18136_bodycap_n2_p0 = 0;
      double v_LoopB_18136_bodycap_n5_p0 = 0;
      sisal_array_t v_LoopB_18136_bodycap_n9_p0 = {0};
      bool v_LoopB_18136_bodycap_n11_p0 = 0;
      sisal_array_t v_LoopB_18136_n__0_A = {0};
      (v_LoopB_18136_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18135_n__0_A));
      int32_t v_LoopB_18136_n__0_N = 0;
      (v_LoopB_18136_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_18135_n__0_N));
      sisal_array_t v_INIT_18184_n__0_A = {0};
      double v_INIT_18184_n__4_EK = 0;
      int32_t v_INIT_18184_n__3_K = 0;
      int32_t v_INIT_18184_n__0_N = 0;
      double v_INIT_18184_n__4_OLD_EK = 0;
      int32_t v_INIT_18184_n__3_OLD_K = 0;
      sisal_array_t v_INIT_18184_n__1_OLD_Z = {0};
      sisal_array_t v_INIT_18184_n__1_Z = {0};
      (v_INIT_18184_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__0_A));
      (v_INIT_18184_n__0_N = SISAL_CAST(int32_t, v_LoopB_18136_n__0_N));
      {
        sisal_array_t v_FORALL_18185_n__0_A = v_INIT_18184_n__0_A;
        int32_t v_FORALL_18185_n__2_J;
        int32_t v_FORALL_18185_n__0_N = v_INIT_18184_n__0_N;
        double v_FORALL_18185_n__3___forall_body_0;
        int32_t v_FORALL_18185_n__2___forall_lb_2_0;
        int32_t v_FORALL_18185_n__2___forall_ub_2_0;
        sisal_array_t v_GENERATOR_18187_n__0_A;
        int32_t v_GENERATOR_18187_n__2_J;
        int32_t v_GENERATOR_18187_n__0_N;
        int32_t v_GENERATOR_18187_n__2___forall_lb_2_0;
        int32_t v_GENERATOR_18187_n__2___forall_ub_2_0;
        sisal_array_t v_BODY_18188_n__0_A;
        int32_t v_BODY_18188_n__0_J;
        int32_t v_BODY_18188_n__0_N;
        int32_t v_BODY_18188_n__0___forall_lb_2_0;
        int32_t v_BODY_18188_n__0___forall_ub_2_0;
        (v_GENERATOR_18187_n__0_N = v_FORALL_18185_n__0_N);
        (v_INIT_18184_n__1_OLD_Z = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_18187_n__0_N - 1) + 1)))));
        (v_INIT_18184_n__1_OLD_Z.dims[0] = ((v_GENERATOR_18187_n__0_N - 1) + 1));
        (v_INIT_18184_n__1_OLD_Z.lower_bound[0] = 1);
        int32_t __g_18185 = 0;
        (v_GENERATOR_18187_n__2___forall_lb_2_0 = 1);
        (v_GENERATOR_18187_n__2___forall_ub_2_0 = v_GENERATOR_18187_n__0_N);
        for ((v_GENERATOR_18187_n__2_J = 1); (v_GENERATOR_18187_n__2_J <= v_GENERATOR_18187_n__0_N); (v_GENERATOR_18187_n__2_J++)) {
          (v_BODY_18188_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_18185_n__0_A));
          (v_BODY_18188_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_18187_n__2_J));
          (v_BODY_18188_n__0_N = SISAL_CAST(int32_t, v_FORALL_18185_n__0_N));
          (v_BODY_18188_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_18187_n__2___forall_lb_2_0));
          (v_BODY_18188_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_18187_n__2___forall_ub_2_0));
          double v_BODY_18188_n__1_p0_o = 0;
          (v_BODY_18188_n__1_p0_o = SISAL_CAST(double, 0.));
          (((double *)v_INIT_18184_n__1_OLD_Z.data)[__g_18185] = SISAL_CAST(double, v_BODY_18188_n__1_p0_o));
          (__g_18185++);
        }
      }
      (v_INIT_18184_n__3_OLD_K = SISAL_CAST(int32_t, 1));
      (v_INIT_18184_n__4_OLD_EK = SISAL_CAST(double, 1.));
      bool v_INIT_18184_n__5_p0_o = 0;
      (v_INIT_18184_n__5_p0_o = SISAL_CAST(bool, true));
      (v_LoopB_18136_n__5_MERGE_EK = v_INIT_18184_n__4_OLD_EK);
      (v_LoopB_18136_n__6_MERGE_K = v_INIT_18184_n__3_OLD_K);
      (v_LoopB_18136_n__7_MERGE_Z = v_INIT_18184_n__1_OLD_Z);
      (v_LoopB_18136_n__8_MERGE_OLD_EK = v_INIT_18184_n__4_OLD_EK);
      (v_LoopB_18136_n__9_MERGE_OLD_K = v_INIT_18184_n__3_OLD_K);
      (v_LoopB_18136_n__10_MERGE_OLD_Z = v_INIT_18184_n__1_OLD_Z);
      (v_LoopB_18136_n__11_MERGE_first = v_INIT_18184_n__5_p0_o);
      sisal_array_t v_TEST_18183_n__0_A = {0};
      double v_TEST_18183_n__0_EK = 0;
      int32_t v_TEST_18183_n__0_K = 0;
      int32_t v_TEST_18183_n__0_N = 0;
      double v_TEST_18183_n__0_OLD_EK = 0;
      int32_t v_TEST_18183_n__0_OLD_K = 0;
      sisal_array_t v_TEST_18183_n__0_OLD_Z = {0};
      sisal_array_t v_TEST_18183_n__0_Z = {0};
      (v_TEST_18183_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__0_A));
      (v_TEST_18183_n__0_EK = SISAL_CAST(double, v_LoopB_18136_n__5_MERGE_EK));
      (v_TEST_18183_n__0_K = SISAL_CAST(int32_t, v_LoopB_18136_n__6_MERGE_K));
      (v_TEST_18183_n__0_N = SISAL_CAST(int32_t, v_LoopB_18136_n__0_N));
      (v_TEST_18183_n__0_OLD_EK = SISAL_CAST(double, v_LoopB_18136_n__8_MERGE_OLD_EK));
      (v_TEST_18183_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_18136_n__9_MERGE_OLD_K));
      (v_TEST_18183_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__10_MERGE_OLD_Z));
      (v_TEST_18183_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__7_MERGE_Z));
      bool v_TEST_18183_n__1_p0_o = 0;
      (v_TEST_18183_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_18183_n__0_K) <= SISAL_CAST(int32_t, v_TEST_18183_n__0_N))));
      #ifdef SISAL_TRAP_ZERO_TRIP
      if ((!v_TEST_18183_n__1_p0_o)) {
        fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_18136 executed 0 times (guard false on entry)\n");
        exit(1);
      }
      #endif
      while (v_TEST_18183_n__1_p0_o) {
        sisal_array_t v_BODY_18137_n__0_A = {0};
        double v_BODY_18137_n__5_EK = 0;
        double v_BODY_18137_n__3_EK1 = 0;
        double v_BODY_18137_n__5_EK2 = 0;
        int32_t v_BODY_18137_n__2_K = 0;
        int32_t v_BODY_18137_n__0_N = 0;
        double v_BODY_18137_n__0_OLD_EK = 0;
        int32_t v_BODY_18137_n__0_OLD_K = 0;
        sisal_array_t v_BODY_18137_n__0_OLD_Z = {0};
        double v_BODY_18137_n__7_S = 0;
        double v_BODY_18137_n__7_SM = 0;
        double v_BODY_18137_n__7_WK = 0;
        double v_BODY_18137_n__7_WKM = 0;
        sisal_array_t v_BODY_18137_n__9_Z = {0};
        sisal_array_t v_BODY_18137_n__5_Z2 = {0};
        sisal_array_t v_BODY_18137_n__9_Z3 = {0};
        double v_BODY_18137_n__0_p1_o = 0;
        sisal_array_t v_BODY_18137_n__0_p7_o = {0};
        (v_BODY_18137_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__0_A));
        (v_BODY_18137_n__0_p1_o = SISAL_CAST(double, v_LoopB_18136_n__5_MERGE_EK));
        int32_t v_BODY_18137_n__0_p2_o = 0;
        (v_BODY_18137_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_18136_n__6_MERGE_K));
        (v_BODY_18137_n__0_N = SISAL_CAST(int32_t, v_LoopB_18136_n__0_N));
        (v_BODY_18137_n__0_OLD_EK = SISAL_CAST(double, v_LoopB_18136_n__8_MERGE_OLD_EK));
        (v_BODY_18137_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_18136_n__9_MERGE_OLD_K));
        (v_BODY_18137_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__10_MERGE_OLD_Z));
        (v_BODY_18137_n__0_p7_o = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__7_MERGE_Z));
        int32_t v_BODY_18137_n__1_p0_o = 0;
        (v_BODY_18137_n__1_p0_o = SISAL_CAST(int32_t, 1));
        (v_BODY_18137_n__2_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_18137_n__0_OLD_K) + SISAL_CAST(int32_t, v_BODY_18137_n__1_p0_o))));
        sisal_array_t v_IF_DOUBLE___18138_n__0_OLD_Z = {0};
        (v_IF_DOUBLE___18138_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_OLD_Z));
        int32_t v_IF_DOUBLE___18138_n__0_OLD_K = 0;
        (v_IF_DOUBLE___18138_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_18137_n__0_OLD_K));
        double v_IF_DOUBLE___18138_n__0_OLD_EK = 0;
        (v_IF_DOUBLE___18138_n__0_OLD_EK = SISAL_CAST(double, v_BODY_18137_n__0_OLD_EK));
        {
          int32_t v_PREDICATE_18139_n__0_OLD_K = 0;
          sisal_array_t v_PREDICATE_18139_n__0_OLD_Z = {0};
          (v_PREDICATE_18139_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___18138_n__0_OLD_Z));
          (v_PREDICATE_18139_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_DOUBLE___18138_n__0_OLD_K));
          double v_PREDICATE_18139_n__1_p0_o = 0;
          (v_PREDICATE_18139_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_18139_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_PREDICATE_18139_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18139_n__0_OLD_Z).lower_bound[0])]));
          double v_PREDICATE_18139_n__2_p0_o = 0;
          (v_PREDICATE_18139_n__2_p0_o = SISAL_CAST(double, 0.));
          bool v_PREDICATE_18139_n__3_p0_o = 0;
          (v_PREDICATE_18139_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_18139_n__1_p0_o) == SISAL_CAST(double, v_PREDICATE_18139_n__2_p0_o))));
          if (v_PREDICATE_18139_n__3_p0_o) {
            double v_THEN_18141_n__0_OLD_EK = 0;
            (v_THEN_18141_n__0_OLD_EK = SISAL_CAST(double, v_IF_DOUBLE___18138_n__0_OLD_EK));
            (v_BODY_18137_n__3_EK1 = SISAL_CAST(double, v_THEN_18141_n__0_OLD_EK));
          }
          else {
            double v_ELSE_18140_n__0_OLD_EK = 0;
            int32_t v_ELSE_18140_n__0_OLD_K = 0;
            sisal_array_t v_ELSE_18140_n__0_OLD_Z = {0};
            (v_ELSE_18140_n__0_OLD_EK = SISAL_CAST(double, v_IF_DOUBLE___18138_n__0_OLD_EK));
            (v_ELSE_18140_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___18138_n__0_OLD_Z));
            (v_ELSE_18140_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_DOUBLE___18138_n__0_OLD_K));
            double v_ELSE_18140_n__1_p0_o = 0;
            (v_ELSE_18140_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18140_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18140_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18140_n__0_OLD_Z).lower_bound[0])]));
            float v_ELSE_18140_n__2_p0_o = 0;
            (v_ELSE_18140_n__2_p0_o = SISAL_CAST(float, (-SISAL_CAST(double, v_ELSE_18140_n__1_p0_o))));
            double v_ELSE_18140_n__3_p0_o = 0;
            (v_ELSE_18140_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18140_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18140_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18140_n__0_OLD_Z).lower_bound[0])]));
            double v_ELSE_18140_n__4_p0_o = 0;
            (v_ELSE_18140_n__4_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_ELSE_18140_n__3_p0_o))));
            double v_ELSE_18140_n__5_p0_o = 0;
            (v_ELSE_18140_n__5_p0_o = SISAL_CAST(double, func_SIGN(SISAL_CAST(double, v_ELSE_18140_n__0_OLD_EK), SISAL_CAST(double, v_ELSE_18140_n__4_p0_o))));
            (v_BODY_18137_n__3_EK1 = SISAL_CAST(double, v_ELSE_18140_n__5_p0_o));
          }
        }
        double v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_EK1 = 0;
        (v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_EK1 = SISAL_CAST(double, v_BODY_18137_n__3_EK1));
        sisal_array_t v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_Z = {0};
        (v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_OLD_Z));
        int32_t v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_K = 0;
        (v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_18137_n__0_OLD_K));
        sisal_array_t v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_A = {0};
        (v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_A));
        int32_t v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_N = 0;
        (v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_N = SISAL_CAST(int32_t, v_BODY_18137_n__0_N));
        {
          sisal_array_t v_PREDICATE_18143_n__0_A = {0};
          double v_PREDICATE_18143_n__0_EK1 = 0;
          int32_t v_PREDICATE_18143_n__0_OLD_K = 0;
          sisal_array_t v_PREDICATE_18143_n__0_OLD_Z = {0};
          (v_PREDICATE_18143_n__0_EK1 = SISAL_CAST(double, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_EK1));
          (v_PREDICATE_18143_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_Z));
          (v_PREDICATE_18143_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_K));
          (v_PREDICATE_18143_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_A));
          double v_PREDICATE_18143_n__1_p0_o = 0;
          (v_PREDICATE_18143_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_PREDICATE_18143_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_OLD_Z).lower_bound[0])]));
          float v_PREDICATE_18143_n__2_p0_o = 0;
          (v_PREDICATE_18143_n__2_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_PREDICATE_18143_n__0_EK1) - SISAL_CAST(double, v_PREDICATE_18143_n__1_p0_o))));
          double v_PREDICATE_18143_n__3_p0_o = 0;
          (v_PREDICATE_18143_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_PREDICATE_18143_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_OLD_Z).lower_bound[0])]));
          double v_PREDICATE_18143_n__4_p0_o = 0;
          (v_PREDICATE_18143_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_PREDICATE_18143_n__0_EK1) - SISAL_CAST(double, v_PREDICATE_18143_n__3_p0_o))));
          double v_PREDICATE_18143_n__5_p0_o = 0;
          (v_PREDICATE_18143_n__5_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_18143_n__4_p0_o))));
          sisal_array_t v_PREDICATE_18143_n__6_p0_o = {0};
          (v_PREDICATE_18143_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_18143_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_A).lower_bound[0]))));
          float v_PREDICATE_18143_n__7_p0_o = 0;
          (v_PREDICATE_18143_n__7_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__6_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_18143_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__6_p0_o).lower_bound[0])]));
          sisal_array_t v_PREDICATE_18143_n__8_p0_o = {0};
          (v_PREDICATE_18143_n__8_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_18143_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__0_A).lower_bound[0]))));
          double v_PREDICATE_18143_n__9_p0_o = 0;
          (v_PREDICATE_18143_n__9_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__8_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_18143_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18143_n__8_p0_o).lower_bound[0])]));
          double v_PREDICATE_18143_n__10_p0_o = 0;
          (v_PREDICATE_18143_n__10_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_18143_n__9_p0_o))));
          bool v_PREDICATE_18143_n__11_p0_o = 0;
          (v_PREDICATE_18143_n__11_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_18143_n__5_p0_o) <= SISAL_CAST(double, v_PREDICATE_18143_n__10_p0_o))));
          if (v_PREDICATE_18143_n__11_p0_o) {
            double v_THEN_18145_n__0_EK1 = 0;
            sisal_array_t v_THEN_18145_n__0_OLD_Z = {0};
            (v_THEN_18145_n__0_EK1 = SISAL_CAST(double, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_EK1));
            (v_THEN_18145_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_Z));
            (v_BODY_18137_n__5_EK2 = SISAL_CAST(double, v_THEN_18145_n__0_EK1));
            (v_BODY_18137_n__5_Z2 = SISAL_CAST(sisal_array_t, v_THEN_18145_n__0_OLD_Z));
          }
          else {
            sisal_array_t v_ELSE_18144_n__0_A = {0};
            double v_ELSE_18144_n__0_EK1 = 0;
            int32_t v_ELSE_18144_n__0_N = 0;
            int32_t v_ELSE_18144_n__0_OLD_K = 0;
            sisal_array_t v_ELSE_18144_n__0_OLD_Z = {0};
            (v_ELSE_18144_n__0_EK1 = SISAL_CAST(double, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_EK1));
            (v_ELSE_18144_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_A));
            (v_ELSE_18144_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_K));
            (v_ELSE_18144_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_OLD_Z));
            (v_ELSE_18144_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE___DOUBLE___18142_n__0_N));
            sisal_array_t v_ELSE_18144_n__1_p0_o = {0};
            (v_ELSE_18144_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            float v_ELSE_18144_n__2_p0_o = 0;
            (v_ELSE_18144_n__2_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__1_p0_o).lower_bound[0])]));
            sisal_array_t v_ELSE_18144_n__3_p0_o = {0};
            (v_ELSE_18144_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            double v_ELSE_18144_n__4_p0_o = 0;
            (v_ELSE_18144_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__3_p0_o).lower_bound[0])]));
            double v_ELSE_18144_n__5_p0_o = 0;
            (v_ELSE_18144_n__5_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__4_p0_o))));
            float v_ELSE_18144_n__6_p0_o = 0;
            (v_ELSE_18144_n__6_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) * SISAL_CAST(double, v_ELSE_18144_n__5_p0_o))));
            sisal_array_t v_ELSE_18144_n__7_p0_o = {0};
            (v_ELSE_18144_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            float v_ELSE_18144_n__8_p0_o = 0;
            (v_ELSE_18144_n__8_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__7_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__7_p0_o).lower_bound[0])]));
            sisal_array_t v_ELSE_18144_n__9_p0_o = {0};
            (v_ELSE_18144_n__9_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            double v_ELSE_18144_n__10_p0_o = 0;
            (v_ELSE_18144_n__10_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__9_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__9_p0_o).lower_bound[0])]));
            double v_ELSE_18144_n__11_p0_o = 0;
            (v_ELSE_18144_n__11_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__10_p0_o))));
            double v_ELSE_18144_n__12_p0_o = 0;
            (v_ELSE_18144_n__12_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) * SISAL_CAST(double, v_ELSE_18144_n__11_p0_o))));
            double v_ELSE_18144_n__13_p0_o = 0;
            (v_ELSE_18144_n__13_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).lower_bound[0])]));
            float v_ELSE_18144_n__14_p0_o = 0;
            (v_ELSE_18144_n__14_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) - SISAL_CAST(double, v_ELSE_18144_n__13_p0_o))));
            double v_ELSE_18144_n__15_p0_o = 0;
            (v_ELSE_18144_n__15_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).lower_bound[0])]));
            double v_ELSE_18144_n__16_p0_o = 0;
            (v_ELSE_18144_n__16_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) - SISAL_CAST(double, v_ELSE_18144_n__15_p0_o))));
            double v_ELSE_18144_n__17_p0_o = 0;
            (v_ELSE_18144_n__17_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__16_p0_o))));
            double v_ELSE_18144_n__18_p0_o = 0;
            (v_ELSE_18144_n__18_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_18144_n__12_p0_o) / SISAL_CAST(double, v_ELSE_18144_n__17_p0_o))));
            int32_t v_ELSE_18144_n__20_p0_o = 0;
            (v_ELSE_18144_n__20_p0_o = SISAL_CAST(int32_t, 1));
            sisal_array_t v_ELSE_18144_n__21_p0_o = {0};
            (v_ELSE_18144_n__21_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            float v_ELSE_18144_n__22_p0_o = 0;
            (v_ELSE_18144_n__22_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__21_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__21_p0_o).lower_bound[0])]));
            sisal_array_t v_ELSE_18144_n__23_p0_o = {0};
            (v_ELSE_18144_n__23_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            double v_ELSE_18144_n__24_p0_o = 0;
            (v_ELSE_18144_n__24_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__23_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__23_p0_o).lower_bound[0])]));
            float v_ELSE_18144_n__25_p0_o = 0;
            (v_ELSE_18144_n__25_p0_o = SISAL_CAST(float, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__24_p0_o))));
            sisal_array_t v_ELSE_18144_n__26_p0_o = {0};
            (v_ELSE_18144_n__26_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            float v_ELSE_18144_n__27_p0_o = 0;
            (v_ELSE_18144_n__27_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__26_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__26_p0_o).lower_bound[0])]));
            sisal_array_t v_ELSE_18144_n__28_p0_o = {0};
            (v_ELSE_18144_n__28_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            double v_ELSE_18144_n__29_p0_o = 0;
            (v_ELSE_18144_n__29_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__28_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__28_p0_o).lower_bound[0])]));
            double v_ELSE_18144_n__30_p0_o = 0;
            (v_ELSE_18144_n__30_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__29_p0_o))));
            double v_ELSE_18144_n__31_p0_o = 0;
            (v_ELSE_18144_n__31_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).lower_bound[0])]));
            float v_ELSE_18144_n__32_p0_o = 0;
            (v_ELSE_18144_n__32_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) - SISAL_CAST(double, v_ELSE_18144_n__31_p0_o))));
            double v_ELSE_18144_n__33_p0_o = 0;
            (v_ELSE_18144_n__33_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).lower_bound[0])]));
            double v_ELSE_18144_n__34_p0_o = 0;
            (v_ELSE_18144_n__34_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) - SISAL_CAST(double, v_ELSE_18144_n__33_p0_o))));
            double v_ELSE_18144_n__35_p0_o = 0;
            (v_ELSE_18144_n__35_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__34_p0_o))));
            float v_ELSE_18144_n__36_p0_o = 0;
            (v_ELSE_18144_n__36_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_ELSE_18144_n__30_p0_o) / SISAL_CAST(double, v_ELSE_18144_n__35_p0_o))));
            int32_t v_ELSE_18144_n__37_p0_o = 0;
            (v_ELSE_18144_n__37_p0_o = SISAL_CAST(int32_t, 1));
            sisal_array_t v_ELSE_18144_n__38_p0_o = {0};
            (v_ELSE_18144_n__38_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            float v_ELSE_18144_n__39_p0_o = 0;
            (v_ELSE_18144_n__39_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__38_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__38_p0_o).lower_bound[0])]));
            sisal_array_t v_ELSE_18144_n__40_p0_o = {0};
            (v_ELSE_18144_n__40_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            double v_ELSE_18144_n__41_p0_o = 0;
            (v_ELSE_18144_n__41_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__40_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__40_p0_o).lower_bound[0])]));
            float v_ELSE_18144_n__42_p0_o = 0;
            (v_ELSE_18144_n__42_p0_o = SISAL_CAST(float, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__41_p0_o))));
            sisal_array_t v_ELSE_18144_n__43_p0_o = {0};
            (v_ELSE_18144_n__43_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            float v_ELSE_18144_n__44_p0_o = 0;
            (v_ELSE_18144_n__44_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__43_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__43_p0_o).lower_bound[0])]));
            sisal_array_t v_ELSE_18144_n__45_p0_o = {0};
            (v_ELSE_18144_n__45_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A), (SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_A).lower_bound[0]))));
            double v_ELSE_18144_n__46_p0_o = 0;
            (v_ELSE_18144_n__46_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__45_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__45_p0_o).lower_bound[0])]));
            double v_ELSE_18144_n__47_p0_o = 0;
            (v_ELSE_18144_n__47_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__46_p0_o))));
            double v_ELSE_18144_n__48_p0_o = 0;
            (v_ELSE_18144_n__48_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).lower_bound[0])]));
            float v_ELSE_18144_n__49_p0_o = 0;
            (v_ELSE_18144_n__49_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) - SISAL_CAST(double, v_ELSE_18144_n__48_p0_o))));
            double v_ELSE_18144_n__50_p0_o = 0;
            (v_ELSE_18144_n__50_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).data)[(SISAL_CAST(int32_t, v_ELSE_18144_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z).lower_bound[0])]));
            double v_ELSE_18144_n__51_p0_o = 0;
            (v_ELSE_18144_n__51_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_18144_n__0_EK1) - SISAL_CAST(double, v_ELSE_18144_n__50_p0_o))));
            double v_ELSE_18144_n__52_p0_o = 0;
            (v_ELSE_18144_n__52_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_18144_n__51_p0_o))));
            double v_ELSE_18144_n__53_p0_o = 0;
            (v_ELSE_18144_n__53_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_18144_n__47_p0_o) / SISAL_CAST(double, v_ELSE_18144_n__52_p0_o))));
            sisal_array_t v_ELSE_18144_n__54_p0_o = {0};
            (v_ELSE_18144_n__54_p0_o = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_ELSE_18144_n__37_p0_o), SISAL_CAST(int32_t, v_ELSE_18144_n__0_N), SISAL_CAST(sisal_array_t, v_ELSE_18144_n__0_OLD_Z), SISAL_CAST(double, v_ELSE_18144_n__53_p0_o))));
            (v_BODY_18137_n__5_EK2 = SISAL_CAST(double, v_ELSE_18144_n__18_p0_o));
            (v_BODY_18137_n__5_Z2 = SISAL_CAST(sisal_array_t, v_ELSE_18144_n__54_p0_o));
          }
        }
        {
          sisal_array_t v_LET_NON_REC_18146_n__0_A = {0};
          double v_LET_NON_REC_18146_n__0_EK = 0;
          double v_LET_NON_REC_18146_n__0_EK1 = 0;
          double v_LET_NON_REC_18146_n__0_EK2 = 0;
          int32_t v_LET_NON_REC_18146_n__0_K = 0;
          int32_t v_LET_NON_REC_18146_n__0_N = 0;
          double v_LET_NON_REC_18146_n__0_OLD_EK = 0;
          int32_t v_LET_NON_REC_18146_n__0_OLD_K = 0;
          sisal_array_t v_LET_NON_REC_18146_n__0_OLD_Z = {0};
          double v_LET_NON_REC_18146_n__6_S1 = 0;
          double v_LET_NON_REC_18146_n__7_SM1 = 0;
          double v_LET_NON_REC_18146_n__2_WK1 = 0;
          double v_LET_NON_REC_18146_n__9_WK2 = 0;
          double v_LET_NON_REC_18146_n__5_WKM1 = 0;
          double v_LET_NON_REC_18146_n__9_WKM2 = 0;
          sisal_array_t v_LET_NON_REC_18146_n__0_Z = {0};
          sisal_array_t v_LET_NON_REC_18146_n__0_Z2 = {0};
          (v_LET_NON_REC_18146_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_A));
          (v_LET_NON_REC_18146_n__0_EK = SISAL_CAST(double, v_BODY_18137_n__0_p1_o));
          (v_LET_NON_REC_18146_n__0_EK1 = SISAL_CAST(double, v_BODY_18137_n__3_EK1));
          (v_LET_NON_REC_18146_n__0_EK2 = SISAL_CAST(double, v_BODY_18137_n__5_EK2));
          (v_LET_NON_REC_18146_n__0_K = SISAL_CAST(int32_t, v_BODY_18137_n__2_K));
          (v_LET_NON_REC_18146_n__0_N = SISAL_CAST(int32_t, v_BODY_18137_n__0_N));
          (v_LET_NON_REC_18146_n__0_OLD_EK = SISAL_CAST(double, v_BODY_18137_n__0_OLD_EK));
          (v_LET_NON_REC_18146_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_18137_n__0_OLD_K));
          (v_LET_NON_REC_18146_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_OLD_Z));
          (v_LET_NON_REC_18146_n__0_Z = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_p7_o));
          (v_LET_NON_REC_18146_n__0_Z2 = SISAL_CAST(sisal_array_t, v_BODY_18137_n__5_Z2));
          double v_LET_NON_REC_18146_n__1_p0_o = 0;
          (v_LET_NON_REC_18146_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_18146_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_18146_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_18146_n__0_Z2).lower_bound[0])]));
          (v_LET_NON_REC_18146_n__2_WK1 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_18146_n__0_EK2) - SISAL_CAST(double, v_LET_NON_REC_18146_n__1_p0_o))));
          double v_LET_NON_REC_18146_n__3_p0_o = 0;
          (v_LET_NON_REC_18146_n__3_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_LET_NON_REC_18146_n__0_EK2))));
          double v_LET_NON_REC_18146_n__4_p0_o = 0;
          (v_LET_NON_REC_18146_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_18146_n__0_Z2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_18146_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_18146_n__0_Z2).lower_bound[0])]));
          (v_LET_NON_REC_18146_n__5_WKM1 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_18146_n__3_p0_o) - SISAL_CAST(double, v_LET_NON_REC_18146_n__4_p0_o))));
          (v_LET_NON_REC_18146_n__6_S1 = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_18146_n__2_WK1))));
          (v_LET_NON_REC_18146_n__7_SM1 = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_18146_n__5_WKM1))));
          double v_LET_NON_REC_18146_n__8_p0_o = 0;
          double v_LET_NON_REC_18146_n__8_p1_o = 0;
          sisal_array_t v_IF_DOUBLE__DOUBLE___18147_n__0_A = {0};
          (v_IF_DOUBLE__DOUBLE___18147_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18146_n__0_A));
          int32_t v_IF_DOUBLE__DOUBLE___18147_n__0_OLD_K = 0;
          (v_IF_DOUBLE__DOUBLE___18147_n__0_OLD_K = SISAL_CAST(int32_t, v_LET_NON_REC_18146_n__0_OLD_K));
          double v_IF_DOUBLE__DOUBLE___18147_n__0_WK1 = 0;
          (v_IF_DOUBLE__DOUBLE___18147_n__0_WK1 = SISAL_CAST(double, v_LET_NON_REC_18146_n__2_WK1));
          double v_IF_DOUBLE__DOUBLE___18147_n__0_WKM1 = 0;
          (v_IF_DOUBLE__DOUBLE___18147_n__0_WKM1 = SISAL_CAST(double, v_LET_NON_REC_18146_n__5_WKM1));
          {
            sisal_array_t v_PREDICATE_18148_n__0_A = {0};
            int32_t v_PREDICATE_18148_n__0_OLD_K = 0;
            (v_PREDICATE_18148_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE___18147_n__0_A));
            (v_PREDICATE_18148_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE___18147_n__0_OLD_K));
            sisal_array_t v_PREDICATE_18148_n__1_p0_o = {0};
            (v_PREDICATE_18148_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_18148_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_18148_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18148_n__0_A).lower_bound[0]))));
            double v_PREDICATE_18148_n__2_p0_o = 0;
            (v_PREDICATE_18148_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_18148_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_18148_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_18148_n__1_p0_o).lower_bound[0])]));
            double v_PREDICATE_18148_n__3_p0_o = 0;
            (v_PREDICATE_18148_n__3_p0_o = SISAL_CAST(double, 0.));
            bool v_PREDICATE_18148_n__4_p0_o = 0;
            (v_PREDICATE_18148_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_18148_n__2_p0_o) != SISAL_CAST(double, v_PREDICATE_18148_n__3_p0_o))));
            if (v_PREDICATE_18148_n__4_p0_o) {
              sisal_array_t v_THEN_18150_n__0_A = {0};
              int32_t v_THEN_18150_n__0_OLD_K = 0;
              double v_THEN_18150_n__0_WK1 = 0;
              double v_THEN_18150_n__0_WKM1 = 0;
              (v_THEN_18150_n__0_WK1 = SISAL_CAST(double, v_IF_DOUBLE__DOUBLE___18147_n__0_WK1));
              (v_THEN_18150_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__DOUBLE___18147_n__0_A));
              (v_THEN_18150_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_DOUBLE__DOUBLE___18147_n__0_OLD_K));
              (v_THEN_18150_n__0_WKM1 = SISAL_CAST(double, v_IF_DOUBLE__DOUBLE___18147_n__0_WKM1));
              sisal_array_t v_THEN_18150_n__1_p0_o = {0};
              (v_THEN_18150_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_THEN_18150_n__0_A), (SISAL_CAST(int32_t, v_THEN_18150_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_18150_n__0_A).lower_bound[0]))));
              double v_THEN_18150_n__2_p0_o = 0;
              (v_THEN_18150_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_18150_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_THEN_18150_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_18150_n__1_p0_o).lower_bound[0])]));
              double v_THEN_18150_n__3_p0_o = 0;
              (v_THEN_18150_n__3_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_18150_n__0_WK1) / SISAL_CAST(double, v_THEN_18150_n__2_p0_o))));
              sisal_array_t v_THEN_18150_n__4_p0_o = {0};
              (v_THEN_18150_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_THEN_18150_n__0_A), (SISAL_CAST(int32_t, v_THEN_18150_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_18150_n__0_A).lower_bound[0]))));
              double v_THEN_18150_n__5_p0_o = 0;
              (v_THEN_18150_n__5_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_18150_n__4_p0_o).data)[(SISAL_CAST(int32_t, v_THEN_18150_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_18150_n__4_p0_o).lower_bound[0])]));
              double v_THEN_18150_n__6_p0_o = 0;
              (v_THEN_18150_n__6_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_18150_n__0_WKM1) / SISAL_CAST(double, v_THEN_18150_n__5_p0_o))));
              (v_LET_NON_REC_18146_n__8_p0_o = SISAL_CAST(double, v_THEN_18150_n__3_p0_o));
              (v_LET_NON_REC_18146_n__8_p1_o = SISAL_CAST(double, v_THEN_18150_n__6_p0_o));
            }
            else {
              double v_ELSE_18149_n__1_p0_o = 0;
              (v_ELSE_18149_n__1_p0_o = SISAL_CAST(double, 1.));
              double v_ELSE_18149_n__2_p0_o = 0;
              (v_ELSE_18149_n__2_p0_o = SISAL_CAST(double, 1.));
              (v_LET_NON_REC_18146_n__8_p0_o = SISAL_CAST(double, v_ELSE_18149_n__1_p0_o));
              (v_LET_NON_REC_18146_n__8_p1_o = SISAL_CAST(double, v_ELSE_18149_n__2_p0_o));
            }
          }
          (v_BODY_18137_n__7_S = SISAL_CAST(double, v_LET_NON_REC_18146_n__6_S1));
          (v_BODY_18137_n__7_SM = SISAL_CAST(double, v_LET_NON_REC_18146_n__7_SM1));
          (v_BODY_18137_n__7_WK = SISAL_CAST(double, v_LET_NON_REC_18146_n__8_p0_o));
          (v_BODY_18137_n__7_WKM = SISAL_CAST(double, v_LET_NON_REC_18146_n__8_p1_o));
        }
        int32_t v_IF_array_dv_DOUBLE____18151_n__0_K = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_K = SISAL_CAST(int32_t, v_BODY_18137_n__2_K));
        int32_t v_IF_array_dv_DOUBLE____18151_n__0_N = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_N = SISAL_CAST(int32_t, v_BODY_18137_n__0_N));
        sisal_array_t v_IF_array_dv_DOUBLE____18151_n__0_A = {0};
        (v_IF_array_dv_DOUBLE____18151_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_A));
        double v_IF_array_dv_DOUBLE____18151_n__0_EK = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_EK = SISAL_CAST(double, v_BODY_18137_n__0_p1_o));
        double v_IF_array_dv_DOUBLE____18151_n__0_EK1 = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_EK1 = SISAL_CAST(double, v_BODY_18137_n__3_EK1));
        double v_IF_array_dv_DOUBLE____18151_n__0_EK2 = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_EK2 = SISAL_CAST(double, v_BODY_18137_n__5_EK2));
        double v_IF_array_dv_DOUBLE____18151_n__0_OLD_EK = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_OLD_EK = SISAL_CAST(double, v_BODY_18137_n__0_OLD_EK));
        int32_t v_IF_array_dv_DOUBLE____18151_n__0_OLD_K = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_18137_n__0_OLD_K));
        sisal_array_t v_IF_array_dv_DOUBLE____18151_n__0_OLD_Z = {0};
        (v_IF_array_dv_DOUBLE____18151_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_OLD_Z));
        double v_IF_array_dv_DOUBLE____18151_n__0_S = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_S = SISAL_CAST(double, v_BODY_18137_n__7_S));
        double v_IF_array_dv_DOUBLE____18151_n__0_SM = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_SM = SISAL_CAST(double, v_BODY_18137_n__7_SM));
        double v_IF_array_dv_DOUBLE____18151_n__0_WK = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_WK = SISAL_CAST(double, v_BODY_18137_n__7_WK));
        double v_IF_array_dv_DOUBLE____18151_n__0_WKM = 0;
        (v_IF_array_dv_DOUBLE____18151_n__0_WKM = SISAL_CAST(double, v_BODY_18137_n__7_WKM));
        sisal_array_t v_IF_array_dv_DOUBLE____18151_n__0_Z = {0};
        (v_IF_array_dv_DOUBLE____18151_n__0_Z = SISAL_CAST(sisal_array_t, v_BODY_18137_n__0_p7_o));
        sisal_array_t v_IF_array_dv_DOUBLE____18151_n__0_Z2 = {0};
        (v_IF_array_dv_DOUBLE____18151_n__0_Z2 = SISAL_CAST(sisal_array_t, v_BODY_18137_n__5_Z2));
        {
          int32_t v_PREDICATE_18152_n__0_K = 0;
          int32_t v_PREDICATE_18152_n__0_N = 0;
          (v_PREDICATE_18152_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18151_n__0_K));
          (v_PREDICATE_18152_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18151_n__0_N));
          bool v_PREDICATE_18152_n__1_p0_o = 0;
          (v_PREDICATE_18152_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_18152_n__0_K) > SISAL_CAST(int32_t, v_PREDICATE_18152_n__0_N))));
          if (v_PREDICATE_18152_n__1_p0_o) {
            int32_t v_THEN_18181_n__0_OLD_K = 0;
            double v_THEN_18181_n__0_WK = 0;
            sisal_array_t v_THEN_18181_n__0_Z2 = {0};
            (v_THEN_18181_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18151_n__0_Z2));
            (v_THEN_18181_n__0_WK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_WK));
            (v_THEN_18181_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18151_n__0_OLD_K));
            sisal_array_t v_THEN_18181_n__1_p0_o = {0};
            (v_THEN_18181_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_18181_n__0_Z2), ((int64_t)SISAL_CAST(int32_t, v_THEN_18181_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_THEN_18181_n__0_WK)))));
            (v_BODY_18137_n__9_Z3 = SISAL_CAST(sisal_array_t, v_THEN_18181_n__1_p0_o));
          }
          else {
            sisal_array_t v_ELSE_18153_n__0_A = {0};
            double v_ELSE_18153_n__0_EK = 0;
            double v_ELSE_18153_n__0_EK1 = 0;
            double v_ELSE_18153_n__0_EK2 = 0;
            int32_t v_ELSE_18153_n__0_K = 0;
            int32_t v_ELSE_18153_n__0_N = 0;
            double v_ELSE_18153_n__0_OLD_EK = 0;
            int32_t v_ELSE_18153_n__0_OLD_K = 0;
            sisal_array_t v_ELSE_18153_n__0_OLD_Z = {0};
            double v_ELSE_18153_n__0_S = 0;
            double v_ELSE_18153_n__0_SM = 0;
            double v_ELSE_18153_n__0_WK = 0;
            double v_ELSE_18153_n__0_WKM = 0;
            sisal_array_t v_ELSE_18153_n__0_Z = {0};
            sisal_array_t v_ELSE_18153_n__0_Z2 = {0};
            (v_ELSE_18153_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18151_n__0_A));
            (v_ELSE_18153_n__0_EK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_EK));
            (v_ELSE_18153_n__0_EK1 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_EK1));
            (v_ELSE_18153_n__0_EK2 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_EK2));
            (v_ELSE_18153_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18151_n__0_K));
            (v_ELSE_18153_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18151_n__0_N));
            (v_ELSE_18153_n__0_OLD_EK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_OLD_EK));
            (v_ELSE_18153_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18151_n__0_OLD_K));
            (v_ELSE_18153_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18151_n__0_OLD_Z));
            (v_ELSE_18153_n__0_S = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_S));
            (v_ELSE_18153_n__0_SM = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_SM));
            (v_ELSE_18153_n__0_WK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_WK));
            (v_ELSE_18153_n__0_WKM = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18151_n__0_WKM));
            (v_ELSE_18153_n__0_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18151_n__0_Z));
            (v_ELSE_18153_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18151_n__0_Z2));
            sisal_array_t v_ELSE_18153_n__1_p0_o = {0};
            {
              sisal_array_t v_LET_NON_REC_18154_n__0_A = {0};
              double v_LET_NON_REC_18154_n__0_EK = 0;
              double v_LET_NON_REC_18154_n__0_EK1 = 0;
              double v_LET_NON_REC_18154_n__0_EK2 = 0;
              int32_t v_LET_NON_REC_18154_n__0_K = 0;
              int32_t v_LET_NON_REC_18154_n__0_N = 0;
              double v_LET_NON_REC_18154_n__0_OLD_EK = 0;
              int32_t v_LET_NON_REC_18154_n__0_OLD_K = 0;
              sisal_array_t v_LET_NON_REC_18154_n__0_OLD_Z = {0};
              double v_LET_NON_REC_18154_n__0_S = 0;
              double v_LET_NON_REC_18154_n__2_S2 = 0;
              double v_LET_NON_REC_18154_n__0_SM = 0;
              double v_LET_NON_REC_18154_n__2_SM2 = 0;
              double v_LET_NON_REC_18154_n__0_WK = 0;
              double v_LET_NON_REC_18154_n__0_WKM = 0;
              sisal_array_t v_LET_NON_REC_18154_n__0_Z = {0};
              sisal_array_t v_LET_NON_REC_18154_n__0_Z2 = {0};
              sisal_array_t v_LET_NON_REC_18154_n__2_Z4 = {0};
              sisal_array_t v_LET_NON_REC_18154_n__4_Z6 = {0};
              (v_LET_NON_REC_18154_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_18153_n__0_A));
              (v_LET_NON_REC_18154_n__0_EK = SISAL_CAST(double, v_ELSE_18153_n__0_EK));
              (v_LET_NON_REC_18154_n__0_EK1 = SISAL_CAST(double, v_ELSE_18153_n__0_EK1));
              (v_LET_NON_REC_18154_n__0_EK2 = SISAL_CAST(double, v_ELSE_18153_n__0_EK2));
              (v_LET_NON_REC_18154_n__0_K = SISAL_CAST(int32_t, v_ELSE_18153_n__0_K));
              (v_LET_NON_REC_18154_n__0_N = SISAL_CAST(int32_t, v_ELSE_18153_n__0_N));
              (v_LET_NON_REC_18154_n__0_OLD_EK = SISAL_CAST(double, v_ELSE_18153_n__0_OLD_EK));
              (v_LET_NON_REC_18154_n__0_OLD_K = SISAL_CAST(int32_t, v_ELSE_18153_n__0_OLD_K));
              (v_LET_NON_REC_18154_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_ELSE_18153_n__0_OLD_Z));
              (v_LET_NON_REC_18154_n__0_S = SISAL_CAST(double, v_ELSE_18153_n__0_S));
              (v_LET_NON_REC_18154_n__0_SM = SISAL_CAST(double, v_ELSE_18153_n__0_SM));
              (v_LET_NON_REC_18154_n__0_WK = SISAL_CAST(double, v_ELSE_18153_n__0_WK));
              (v_LET_NON_REC_18154_n__0_WKM = SISAL_CAST(double, v_ELSE_18153_n__0_WKM));
              (v_LET_NON_REC_18154_n__0_Z = SISAL_CAST(sisal_array_t, v_ELSE_18153_n__0_Z));
              (v_LET_NON_REC_18154_n__0_Z2 = SISAL_CAST(sisal_array_t, v_ELSE_18153_n__0_Z2));
              sisal_array_t v_LET_NON_REC_18154_n__1_p0_o = {0};
              double v_LET_NON_REC_18154_n__1_p1_o = 0;
              double v_LET_NON_REC_18154_n__1_p2_o = 0;
              {
                sisal_array_t v_LET_NON_REC_18155_n__0_A = {0};
                double v_LET_NON_REC_18155_n__0_EK = 0;
                double v_LET_NON_REC_18155_n__0_EK1 = 0;
                double v_LET_NON_REC_18155_n__0_EK2 = 0;
                int32_t v_LET_NON_REC_18155_n__0_K = 0;
                int32_t v_LET_NON_REC_18155_n__0_N = 0;
                double v_LET_NON_REC_18155_n__0_OLD_EK = 0;
                int32_t v_LET_NON_REC_18155_n__0_OLD_K = 0;
                sisal_array_t v_LET_NON_REC_18155_n__0_OLD_Z = {0};
                double v_LET_NON_REC_18155_n__0_S = 0;
                double v_LET_NON_REC_18155_n__6_S3 = 0;
                double v_LET_NON_REC_18155_n__0_SM = 0;
                double v_LET_NON_REC_18155_n__4_SM3 = 0;
                double v_LET_NON_REC_18155_n__0_WK = 0;
                double v_LET_NON_REC_18155_n__0_WKM = 0;
                sisal_array_t v_LET_NON_REC_18155_n__0_Z = {0};
                sisal_array_t v_LET_NON_REC_18155_n__0_Z2 = {0};
                sisal_array_t v_LET_NON_REC_18155_n__4_Z5 = {0};
                sisal_array_t v_LET_NON_REC_18155_n__2_Z5INIT = {0};
                (v_LET_NON_REC_18155_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_A));
                (v_LET_NON_REC_18155_n__0_EK = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_EK));
                (v_LET_NON_REC_18155_n__0_EK1 = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_EK1));
                (v_LET_NON_REC_18155_n__0_EK2 = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_EK2));
                (v_LET_NON_REC_18155_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_18154_n__0_K));
                (v_LET_NON_REC_18155_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_18154_n__0_N));
                (v_LET_NON_REC_18155_n__0_OLD_EK = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_OLD_EK));
                (v_LET_NON_REC_18155_n__0_OLD_K = SISAL_CAST(int32_t, v_LET_NON_REC_18154_n__0_OLD_K));
                (v_LET_NON_REC_18155_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_OLD_Z));
                (v_LET_NON_REC_18155_n__0_S = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_S));
                (v_LET_NON_REC_18155_n__0_SM = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_SM));
                (v_LET_NON_REC_18155_n__0_WK = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_WK));
                (v_LET_NON_REC_18155_n__0_WKM = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_WKM));
                (v_LET_NON_REC_18155_n__0_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_Z));
                (v_LET_NON_REC_18155_n__0_Z2 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_Z2));
                sisal_array_t v_LET_NON_REC_18155_n__1_p0_o = {0};
                {
                  sisal_array_t v_FORALL_18156_n__0_A = v_LET_NON_REC_18155_n__0_A;
                  double v_FORALL_18156_n__0_EK = v_LET_NON_REC_18155_n__0_EK;
                  double v_FORALL_18156_n__0_EK1 = v_LET_NON_REC_18155_n__0_EK1;
                  double v_FORALL_18156_n__0_EK2 = v_LET_NON_REC_18155_n__0_EK2;
                  int32_t v_FORALL_18156_n__2_J;
                  int32_t v_FORALL_18156_n__0_K = v_LET_NON_REC_18155_n__0_K;
                  int32_t v_FORALL_18156_n__0_N = v_LET_NON_REC_18155_n__0_N;
                  double v_FORALL_18156_n__0_OLD_EK = v_LET_NON_REC_18155_n__0_OLD_EK;
                  int32_t v_FORALL_18156_n__0_OLD_K = v_LET_NON_REC_18155_n__0_OLD_K;
                  sisal_array_t v_FORALL_18156_n__0_OLD_Z = v_LET_NON_REC_18155_n__0_OLD_Z;
                  double v_FORALL_18156_n__0_S = v_LET_NON_REC_18155_n__0_S;
                  double v_FORALL_18156_n__0_SM = v_LET_NON_REC_18155_n__0_SM;
                  double v_FORALL_18156_n__0_WK = v_LET_NON_REC_18155_n__0_WK;
                  double v_FORALL_18156_n__0_WKM = v_LET_NON_REC_18155_n__0_WKM;
                  sisal_array_t v_FORALL_18156_n__0_Z = v_LET_NON_REC_18155_n__0_Z;
                  sisal_array_t v_FORALL_18156_n__0_Z2 = v_LET_NON_REC_18155_n__0_Z2;
                  double v_FORALL_18156_n__3___forall_body_0;
                  int32_t v_FORALL_18156_n__2___forall_lb_2_0;
                  int32_t v_FORALL_18156_n__2___forall_ub_2_0;
                  sisal_array_t v_GENERATOR_18158_n__0_A;
                  double v_GENERATOR_18158_n__0_EK;
                  double v_GENERATOR_18158_n__0_EK1;
                  double v_GENERATOR_18158_n__0_EK2;
                  int32_t v_GENERATOR_18158_n__2_J;
                  int32_t v_GENERATOR_18158_n__0_K;
                  int32_t v_GENERATOR_18158_n__0_N;
                  double v_GENERATOR_18158_n__0_OLD_EK;
                  int32_t v_GENERATOR_18158_n__0_OLD_K;
                  sisal_array_t v_GENERATOR_18158_n__0_OLD_Z;
                  double v_GENERATOR_18158_n__0_S;
                  double v_GENERATOR_18158_n__0_SM;
                  double v_GENERATOR_18158_n__0_WK;
                  double v_GENERATOR_18158_n__0_WKM;
                  sisal_array_t v_GENERATOR_18158_n__0_Z;
                  sisal_array_t v_GENERATOR_18158_n__0_Z2;
                  int32_t v_GENERATOR_18158_n__2___forall_lb_2_0;
                  int32_t v_GENERATOR_18158_n__2___forall_ub_2_0;
                  sisal_array_t v_BODY_18159_n__0_A;
                  double v_BODY_18159_n__0_EK;
                  double v_BODY_18159_n__0_EK1;
                  double v_BODY_18159_n__0_EK2;
                  int32_t v_BODY_18159_n__0_J;
                  int32_t v_BODY_18159_n__0_K;
                  int32_t v_BODY_18159_n__0_N;
                  double v_BODY_18159_n__0_OLD_EK;
                  int32_t v_BODY_18159_n__0_OLD_K;
                  sisal_array_t v_BODY_18159_n__0_OLD_Z;
                  double v_BODY_18159_n__0_S;
                  double v_BODY_18159_n__0_SM;
                  double v_BODY_18159_n__0_WK;
                  double v_BODY_18159_n__0_WKM;
                  sisal_array_t v_BODY_18159_n__0_Z;
                  sisal_array_t v_BODY_18159_n__0_Z2;
                  int32_t v_BODY_18159_n__0___forall_lb_2_0;
                  int32_t v_BODY_18159_n__0___forall_ub_2_0;
                  (v_GENERATOR_18158_n__0_OLD_K = v_FORALL_18156_n__0_OLD_K);
                  (v_LET_NON_REC_18155_n__1_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_18158_n__0_OLD_K - 1) + 1)))));
                  (v_LET_NON_REC_18155_n__1_p0_o.dims[0] = ((v_GENERATOR_18158_n__0_OLD_K - 1) + 1));
                  (v_LET_NON_REC_18155_n__1_p0_o.lower_bound[0] = 1);
                  int32_t __g_18156 = 0;
                  (v_GENERATOR_18158_n__2___forall_lb_2_0 = 1);
                  (v_GENERATOR_18158_n__2___forall_ub_2_0 = v_GENERATOR_18158_n__0_OLD_K);
                  for ((v_GENERATOR_18158_n__2_J = 1); (v_GENERATOR_18158_n__2_J <= v_GENERATOR_18158_n__0_OLD_K); (v_GENERATOR_18158_n__2_J++)) {
                    (v_BODY_18159_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_18156_n__0_A));
                    (v_BODY_18159_n__0_EK = SISAL_CAST(double, v_FORALL_18156_n__0_EK));
                    (v_BODY_18159_n__0_EK1 = SISAL_CAST(double, v_FORALL_18156_n__0_EK1));
                    (v_BODY_18159_n__0_EK2 = SISAL_CAST(double, v_FORALL_18156_n__0_EK2));
                    (v_BODY_18159_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_18158_n__2_J));
                    (v_BODY_18159_n__0_K = SISAL_CAST(int32_t, v_FORALL_18156_n__0_K));
                    (v_BODY_18159_n__0_N = SISAL_CAST(int32_t, v_FORALL_18156_n__0_N));
                    (v_BODY_18159_n__0_OLD_EK = SISAL_CAST(double, v_FORALL_18156_n__0_OLD_EK));
                    (v_BODY_18159_n__0_OLD_K = SISAL_CAST(int32_t, v_FORALL_18156_n__0_OLD_K));
                    (v_BODY_18159_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_FORALL_18156_n__0_OLD_Z));
                    (v_BODY_18159_n__0_S = SISAL_CAST(double, v_FORALL_18156_n__0_S));
                    (v_BODY_18159_n__0_SM = SISAL_CAST(double, v_FORALL_18156_n__0_SM));
                    (v_BODY_18159_n__0_WK = SISAL_CAST(double, v_FORALL_18156_n__0_WK));
                    (v_BODY_18159_n__0_WKM = SISAL_CAST(double, v_FORALL_18156_n__0_WKM));
                    (v_BODY_18159_n__0_Z = SISAL_CAST(sisal_array_t, v_FORALL_18156_n__0_Z));
                    (v_BODY_18159_n__0_Z2 = SISAL_CAST(sisal_array_t, v_FORALL_18156_n__0_Z2));
                    (v_BODY_18159_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_18158_n__2___forall_lb_2_0));
                    (v_BODY_18159_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_18158_n__2___forall_ub_2_0));
                    double v_BODY_18159_n__1_p0_o = 0;
                    (v_BODY_18159_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18159_n__0_Z2).data)[(SISAL_CAST(int32_t, v_BODY_18159_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18159_n__0_Z2).lower_bound[0])]));
                    (((double *)v_LET_NON_REC_18155_n__1_p0_o.data)[__g_18156] = SISAL_CAST(double, v_BODY_18159_n__1_p0_o));
                    (__g_18156++);
                  }
                }
                sisal_array_t v_LET_NON_REC_18155_n__3_p0_o = {0};
                double v_LET_NON_REC_18155_n__3_p1_o = 0;
                {
                  sisal_array_t v_FORALL_18160_n__0_A = v_LET_NON_REC_18155_n__0_A;
                  double v_FORALL_18160_n__0_EK = v_LET_NON_REC_18155_n__0_EK;
                  double v_FORALL_18160_n__0_EK1 = v_LET_NON_REC_18155_n__0_EK1;
                  double v_FORALL_18160_n__0_EK2 = v_LET_NON_REC_18155_n__0_EK2;
                  int32_t v_FORALL_18160_n__2_J;
                  int32_t v_FORALL_18160_n__0_K = v_LET_NON_REC_18155_n__0_K;
                  int32_t v_FORALL_18160_n__0_N = v_LET_NON_REC_18155_n__0_N;
                  double v_FORALL_18160_n__0_OLD_EK = v_LET_NON_REC_18155_n__0_OLD_EK;
                  int32_t v_FORALL_18160_n__0_OLD_K = v_LET_NON_REC_18155_n__0_OLD_K;
                  sisal_array_t v_FORALL_18160_n__0_OLD_Z = v_LET_NON_REC_18155_n__0_OLD_Z;
                  double v_FORALL_18160_n__0_S = v_LET_NON_REC_18155_n__0_S;
                  double v_FORALL_18160_n__0_SM = v_LET_NON_REC_18155_n__0_SM;
                  double v_FORALL_18160_n__0_WK = v_LET_NON_REC_18155_n__0_WK;
                  double v_FORALL_18160_n__0_WKM = v_LET_NON_REC_18155_n__0_WKM;
                  sisal_array_t v_FORALL_18160_n__0_Z = v_LET_NON_REC_18155_n__0_Z;
                  sisal_array_t v_FORALL_18160_n__0_Z2 = v_LET_NON_REC_18155_n__0_Z2;
                  sisal_array_t v_FORALL_18160_n__0_Z5INIT = v_LET_NON_REC_18155_n__1_p0_o;
                  double v_FORALL_18160_n__3___forall_body_0;
                  double v_FORALL_18160_n__3___forall_body_1;
                  int32_t v_FORALL_18160_n__2___forall_lb_1_0;
                  int32_t v_FORALL_18160_n__2___forall_ub_1_0;
                  sisal_array_t v_GENERATOR_18162_n__0_A;
                  double v_GENERATOR_18162_n__0_EK;
                  double v_GENERATOR_18162_n__0_EK1;
                  double v_GENERATOR_18162_n__0_EK2;
                  int32_t v_GENERATOR_18162_n__1_J;
                  int32_t v_GENERATOR_18162_n__0_K;
                  int32_t v_GENERATOR_18162_n__0_N;
                  double v_GENERATOR_18162_n__0_OLD_EK;
                  int32_t v_GENERATOR_18162_n__0_OLD_K;
                  sisal_array_t v_GENERATOR_18162_n__0_OLD_Z;
                  double v_GENERATOR_18162_n__0_S;
                  double v_GENERATOR_18162_n__0_SM;
                  double v_GENERATOR_18162_n__0_WK;
                  double v_GENERATOR_18162_n__0_WKM;
                  sisal_array_t v_GENERATOR_18162_n__0_Z;
                  sisal_array_t v_GENERATOR_18162_n__0_Z2;
                  sisal_array_t v_GENERATOR_18162_n__0_Z5INIT;
                  int32_t v_GENERATOR_18162_n__1___forall_lb_1_0;
                  int32_t v_GENERATOR_18162_n__1___forall_ub_1_0;
                  sisal_array_t v_BODY_18163_n__0_A;
                  double v_BODY_18163_n__0_EK;
                  double v_BODY_18163_n__0_EK1;
                  double v_BODY_18163_n__0_EK2;
                  int32_t v_BODY_18163_n__0_J;
                  int32_t v_BODY_18163_n__0_K;
                  int32_t v_BODY_18163_n__0_N;
                  double v_BODY_18163_n__0_OLD_EK;
                  int32_t v_BODY_18163_n__0_OLD_K;
                  sisal_array_t v_BODY_18163_n__0_OLD_Z;
                  double v_BODY_18163_n__0_S;
                  double v_BODY_18163_n__0_SM;
                  double v_BODY_18163_n__0_WK;
                  double v_BODY_18163_n__0_WKM;
                  sisal_array_t v_BODY_18163_n__0_Z;
                  sisal_array_t v_BODY_18163_n__0_Z2;
                  sisal_array_t v_BODY_18163_n__0_Z5INIT;
                  int32_t v_BODY_18163_n__0___forall_lb_1_0;
                  int32_t v_BODY_18163_n__0___forall_ub_1_0;
                  (v_GENERATOR_18162_n__0_K = v_FORALL_18160_n__0_K);
                  (v_GENERATOR_18162_n__0_N = v_FORALL_18160_n__0_N);
                  (v_LET_NON_REC_18155_n__3_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_18162_n__0_N - v_GENERATOR_18162_n__0_K) + 1)))));
                  (v_LET_NON_REC_18155_n__3_p0_o.dims[0] = ((v_GENERATOR_18162_n__0_N - v_GENERATOR_18162_n__0_K) + 1));
                  (v_LET_NON_REC_18155_n__3_p0_o.lower_bound[0] = v_GENERATOR_18162_n__0_K);
                  (v_LET_NON_REC_18155_n__3_p1_o = 0);
                  int32_t __g_18160 = 0;
                  (v_GENERATOR_18162_n__1___forall_lb_1_0 = v_GENERATOR_18162_n__0_K);
                  (v_GENERATOR_18162_n__1___forall_ub_1_0 = v_GENERATOR_18162_n__0_N);
                  for ((v_GENERATOR_18162_n__1_J = v_GENERATOR_18162_n__0_K); (v_GENERATOR_18162_n__1_J <= v_GENERATOR_18162_n__0_N); (v_GENERATOR_18162_n__1_J++)) {
                    (v_BODY_18163_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_18160_n__0_A));
                    (v_BODY_18163_n__0_EK = SISAL_CAST(double, v_FORALL_18160_n__0_EK));
                    (v_BODY_18163_n__0_EK1 = SISAL_CAST(double, v_FORALL_18160_n__0_EK1));
                    (v_BODY_18163_n__0_EK2 = SISAL_CAST(double, v_FORALL_18160_n__0_EK2));
                    (v_BODY_18163_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_18162_n__1_J));
                    (v_BODY_18163_n__0_K = SISAL_CAST(int32_t, v_FORALL_18160_n__0_K));
                    (v_BODY_18163_n__0_N = SISAL_CAST(int32_t, v_FORALL_18160_n__0_N));
                    (v_BODY_18163_n__0_OLD_EK = SISAL_CAST(double, v_FORALL_18160_n__0_OLD_EK));
                    (v_BODY_18163_n__0_OLD_K = SISAL_CAST(int32_t, v_FORALL_18160_n__0_OLD_K));
                    (v_BODY_18163_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_FORALL_18160_n__0_OLD_Z));
                    (v_BODY_18163_n__0_S = SISAL_CAST(double, v_FORALL_18160_n__0_S));
                    (v_BODY_18163_n__0_SM = SISAL_CAST(double, v_FORALL_18160_n__0_SM));
                    (v_BODY_18163_n__0_WK = SISAL_CAST(double, v_FORALL_18160_n__0_WK));
                    (v_BODY_18163_n__0_WKM = SISAL_CAST(double, v_FORALL_18160_n__0_WKM));
                    (v_BODY_18163_n__0_Z = SISAL_CAST(sisal_array_t, v_FORALL_18160_n__0_Z));
                    (v_BODY_18163_n__0_Z2 = SISAL_CAST(sisal_array_t, v_FORALL_18160_n__0_Z2));
                    (v_BODY_18163_n__0_Z5INIT = SISAL_CAST(sisal_array_t, v_FORALL_18160_n__0_Z5INIT));
                    (v_BODY_18163_n__0___forall_lb_1_0 = SISAL_CAST(int32_t, v_GENERATOR_18162_n__1___forall_lb_1_0));
                    (v_BODY_18163_n__0___forall_ub_1_0 = SISAL_CAST(int32_t, v_GENERATOR_18162_n__1___forall_ub_1_0));
                    double v_BODY_18163_n__1_p0_o = 0;
                    (v_BODY_18163_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_Z2).data)[(SISAL_CAST(int32_t, v_BODY_18163_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_Z2).lower_bound[0])]));
                    sisal_array_t v_BODY_18163_n__2_p0_o = {0};
                    (v_BODY_18163_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_A), (SISAL_CAST(int32_t, v_BODY_18163_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_A).lower_bound[0]))));
                    double v_BODY_18163_n__3_p0_o = 0;
                    (v_BODY_18163_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18163_n__2_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_18163_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__2_p0_o).lower_bound[0])]));
                    double v_BODY_18163_n__4_p0_o = 0;
                    (v_BODY_18163_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18163_n__0_WK) * SISAL_CAST(double, v_BODY_18163_n__3_p0_o))));
                    double v_BODY_18163_n__5_p0_o = 0;
                    (v_BODY_18163_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18163_n__1_p0_o) + SISAL_CAST(double, v_BODY_18163_n__4_p0_o))));
                    double v_BODY_18163_n__6_p0_o = 0;
                    (v_BODY_18163_n__6_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_Z2).data)[(SISAL_CAST(int32_t, v_BODY_18163_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_Z2).lower_bound[0])]));
                    sisal_array_t v_BODY_18163_n__7_p0_o = {0};
                    (v_BODY_18163_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_A), (SISAL_CAST(int32_t, v_BODY_18163_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_A).lower_bound[0]))));
                    double v_BODY_18163_n__8_p0_o = 0;
                    (v_BODY_18163_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18163_n__7_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_18163_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__7_p0_o).lower_bound[0])]));
                    double v_BODY_18163_n__9_p0_o = 0;
                    (v_BODY_18163_n__9_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18163_n__0_WKM) * SISAL_CAST(double, v_BODY_18163_n__8_p0_o))));
                    float v_BODY_18163_n__10_p0_o = 0;
                    (v_BODY_18163_n__10_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_BODY_18163_n__6_p0_o) + SISAL_CAST(double, v_BODY_18163_n__9_p0_o))));
                    double v_BODY_18163_n__11_p0_o = 0;
                    (v_BODY_18163_n__11_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_Z2).data)[(SISAL_CAST(int32_t, v_BODY_18163_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_Z2).lower_bound[0])]));
                    sisal_array_t v_BODY_18163_n__12_p0_o = {0};
                    (v_BODY_18163_n__12_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_A), (SISAL_CAST(int32_t, v_BODY_18163_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__0_A).lower_bound[0]))));
                    double v_BODY_18163_n__13_p0_o = 0;
                    (v_BODY_18163_n__13_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18163_n__12_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_18163_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18163_n__12_p0_o).lower_bound[0])]));
                    double v_BODY_18163_n__14_p0_o = 0;
                    (v_BODY_18163_n__14_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18163_n__0_WKM) * SISAL_CAST(double, v_BODY_18163_n__13_p0_o))));
                    double v_BODY_18163_n__15_p0_o = 0;
                    (v_BODY_18163_n__15_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18163_n__11_p0_o) + SISAL_CAST(double, v_BODY_18163_n__14_p0_o))));
                    double v_BODY_18163_n__16_p0_o = 0;
                    (v_BODY_18163_n__16_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_18163_n__15_p0_o))));
                    (((double *)v_LET_NON_REC_18155_n__3_p0_o.data)[__g_18160] = SISAL_CAST(double, v_BODY_18163_n__5_p0_o));
                    (v_LET_NON_REC_18155_n__3_p1_o = (v_LET_NON_REC_18155_n__3_p1_o + SISAL_CAST(double, v_BODY_18163_n__16_p0_o)));
                    (__g_18160++);
                  }
                }
                double v_LET_NON_REC_18155_n__5_p0_o = 0;
                {
                  sisal_array_t v_FORALL_18164_n__0_A = v_LET_NON_REC_18155_n__0_A;
                  double v_FORALL_18164_n__0_EK = v_LET_NON_REC_18155_n__0_EK;
                  double v_FORALL_18164_n__0_EK1 = v_LET_NON_REC_18155_n__0_EK1;
                  double v_FORALL_18164_n__0_EK2 = v_LET_NON_REC_18155_n__0_EK2;
                  int32_t v_FORALL_18164_n__2_J;
                  int32_t v_FORALL_18164_n__0_K = v_LET_NON_REC_18155_n__0_K;
                  int32_t v_FORALL_18164_n__0_N = v_LET_NON_REC_18155_n__0_N;
                  double v_FORALL_18164_n__0_OLD_EK = v_LET_NON_REC_18155_n__0_OLD_EK;
                  int32_t v_FORALL_18164_n__0_OLD_K = v_LET_NON_REC_18155_n__0_OLD_K;
                  sisal_array_t v_FORALL_18164_n__0_OLD_Z = v_LET_NON_REC_18155_n__0_OLD_Z;
                  double v_FORALL_18164_n__0_S = v_LET_NON_REC_18155_n__0_S;
                  double v_FORALL_18164_n__0_SM = v_LET_NON_REC_18155_n__0_SM;
                  double v_FORALL_18164_n__0_SM3 = v_LET_NON_REC_18155_n__3_p1_o;
                  double v_FORALL_18164_n__0_WK = v_LET_NON_REC_18155_n__0_WK;
                  double v_FORALL_18164_n__0_WKM = v_LET_NON_REC_18155_n__0_WKM;
                  sisal_array_t v_FORALL_18164_n__0_Z = v_LET_NON_REC_18155_n__0_Z;
                  sisal_array_t v_FORALL_18164_n__0_Z2 = v_LET_NON_REC_18155_n__0_Z2;
                  sisal_array_t v_FORALL_18164_n__0_Z5 = v_LET_NON_REC_18155_n__3_p0_o;
                  sisal_array_t v_FORALL_18164_n__0_Z5INIT = v_LET_NON_REC_18155_n__1_p0_o;
                  double v_FORALL_18164_n__3___forall_body_0;
                  int32_t v_FORALL_18164_n__2___forall_lb_1_0;
                  int32_t v_FORALL_18164_n__2___forall_ub_1_0;
                  sisal_array_t v_GENERATOR_18166_n__0_A;
                  double v_GENERATOR_18166_n__0_EK;
                  double v_GENERATOR_18166_n__0_EK1;
                  double v_GENERATOR_18166_n__0_EK2;
                  int32_t v_GENERATOR_18166_n__1_J;
                  int32_t v_GENERATOR_18166_n__0_K;
                  int32_t v_GENERATOR_18166_n__0_N;
                  double v_GENERATOR_18166_n__0_OLD_EK;
                  int32_t v_GENERATOR_18166_n__0_OLD_K;
                  sisal_array_t v_GENERATOR_18166_n__0_OLD_Z;
                  double v_GENERATOR_18166_n__0_S;
                  double v_GENERATOR_18166_n__0_SM;
                  double v_GENERATOR_18166_n__0_SM3;
                  double v_GENERATOR_18166_n__0_WK;
                  double v_GENERATOR_18166_n__0_WKM;
                  sisal_array_t v_GENERATOR_18166_n__0_Z;
                  sisal_array_t v_GENERATOR_18166_n__0_Z2;
                  sisal_array_t v_GENERATOR_18166_n__0_Z5;
                  sisal_array_t v_GENERATOR_18166_n__0_Z5INIT;
                  int32_t v_GENERATOR_18166_n__1___forall_lb_1_0;
                  int32_t v_GENERATOR_18166_n__1___forall_ub_1_0;
                  sisal_array_t v_BODY_18167_n__0_A;
                  double v_BODY_18167_n__0_EK;
                  double v_BODY_18167_n__0_EK1;
                  double v_BODY_18167_n__0_EK2;
                  int32_t v_BODY_18167_n__0_J;
                  int32_t v_BODY_18167_n__0_K;
                  int32_t v_BODY_18167_n__0_N;
                  double v_BODY_18167_n__0_OLD_EK;
                  int32_t v_BODY_18167_n__0_OLD_K;
                  sisal_array_t v_BODY_18167_n__0_OLD_Z;
                  double v_BODY_18167_n__0_S;
                  double v_BODY_18167_n__0_SM;
                  double v_BODY_18167_n__0_SM3;
                  double v_BODY_18167_n__0_WK;
                  double v_BODY_18167_n__0_WKM;
                  sisal_array_t v_BODY_18167_n__0_Z;
                  sisal_array_t v_BODY_18167_n__0_Z2;
                  sisal_array_t v_BODY_18167_n__0_Z5;
                  sisal_array_t v_BODY_18167_n__0_Z5INIT;
                  int32_t v_BODY_18167_n__0___forall_lb_1_0;
                  int32_t v_BODY_18167_n__0___forall_ub_1_0;
                  (v_GENERATOR_18166_n__0_K = v_FORALL_18164_n__0_K);
                  (v_GENERATOR_18166_n__0_N = v_FORALL_18164_n__0_N);
                  (v_LET_NON_REC_18155_n__5_p0_o = 0);
                  (v_GENERATOR_18166_n__1___forall_lb_1_0 = v_GENERATOR_18166_n__0_K);
                  (v_GENERATOR_18166_n__1___forall_ub_1_0 = v_GENERATOR_18166_n__0_N);
                  for ((v_GENERATOR_18166_n__1_J = v_GENERATOR_18166_n__0_K); (v_GENERATOR_18166_n__1_J <= v_GENERATOR_18166_n__0_N); (v_GENERATOR_18166_n__1_J++)) {
                    (v_BODY_18167_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_18164_n__0_A));
                    (v_BODY_18167_n__0_EK = SISAL_CAST(double, v_FORALL_18164_n__0_EK));
                    (v_BODY_18167_n__0_EK1 = SISAL_CAST(double, v_FORALL_18164_n__0_EK1));
                    (v_BODY_18167_n__0_EK2 = SISAL_CAST(double, v_FORALL_18164_n__0_EK2));
                    (v_BODY_18167_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_18166_n__1_J));
                    (v_BODY_18167_n__0_K = SISAL_CAST(int32_t, v_FORALL_18164_n__0_K));
                    (v_BODY_18167_n__0_N = SISAL_CAST(int32_t, v_FORALL_18164_n__0_N));
                    (v_BODY_18167_n__0_OLD_EK = SISAL_CAST(double, v_FORALL_18164_n__0_OLD_EK));
                    (v_BODY_18167_n__0_OLD_K = SISAL_CAST(int32_t, v_FORALL_18164_n__0_OLD_K));
                    (v_BODY_18167_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_FORALL_18164_n__0_OLD_Z));
                    (v_BODY_18167_n__0_S = SISAL_CAST(double, v_FORALL_18164_n__0_S));
                    (v_BODY_18167_n__0_SM = SISAL_CAST(double, v_FORALL_18164_n__0_SM));
                    (v_BODY_18167_n__0_SM3 = SISAL_CAST(double, v_FORALL_18164_n__0_SM3));
                    (v_BODY_18167_n__0_WK = SISAL_CAST(double, v_FORALL_18164_n__0_WK));
                    (v_BODY_18167_n__0_WKM = SISAL_CAST(double, v_FORALL_18164_n__0_WKM));
                    (v_BODY_18167_n__0_Z = SISAL_CAST(sisal_array_t, v_FORALL_18164_n__0_Z));
                    (v_BODY_18167_n__0_Z2 = SISAL_CAST(sisal_array_t, v_FORALL_18164_n__0_Z2));
                    (v_BODY_18167_n__0_Z5 = SISAL_CAST(sisal_array_t, v_FORALL_18164_n__0_Z5));
                    (v_BODY_18167_n__0_Z5INIT = SISAL_CAST(sisal_array_t, v_FORALL_18164_n__0_Z5INIT));
                    (v_BODY_18167_n__0___forall_lb_1_0 = SISAL_CAST(int32_t, v_GENERATOR_18166_n__1___forall_lb_1_0));
                    (v_BODY_18167_n__0___forall_ub_1_0 = SISAL_CAST(int32_t, v_GENERATOR_18166_n__1___forall_ub_1_0));
                    float v_BODY_18167_n__1_p0_o = 0;
                    (v_BODY_18167_n__1_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_18167_n__0_Z5).data)[(SISAL_CAST(int32_t, v_BODY_18167_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18167_n__0_Z5).lower_bound[0])]));
                    double v_BODY_18167_n__2_p0_o = 0;
                    (v_BODY_18167_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18167_n__0_Z5).data)[(SISAL_CAST(int32_t, v_BODY_18167_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18167_n__0_Z5).lower_bound[0])]));
                    double v_BODY_18167_n__3_p0_o = 0;
                    (v_BODY_18167_n__3_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_BODY_18167_n__2_p0_o))));
                    (v_LET_NON_REC_18155_n__5_p0_o = (v_LET_NON_REC_18155_n__5_p0_o + SISAL_CAST(double, v_BODY_18167_n__3_p0_o)));
                  }
                }
                sisal_array_t v_LET_NON_REC_18155_n__7_p0_o = {0};
                (v_LET_NON_REC_18155_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_addh_arr(SISAL_CAST(sisal_array_t, v_LET_NON_REC_18155_n__1_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_18155_n__3_p0_o))));
                double v_LET_NON_REC_18155_n__8_p0_o = 0;
                (v_LET_NON_REC_18155_n__8_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_18155_n__3_p1_o) + SISAL_CAST(double, v_LET_NON_REC_18155_n__0_SM))));
                double v_LET_NON_REC_18155_n__9_p0_o = 0;
                (v_LET_NON_REC_18155_n__9_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_18155_n__5_p0_o) + SISAL_CAST(double, v_LET_NON_REC_18155_n__0_S))));
                (v_LET_NON_REC_18154_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18155_n__7_p0_o));
                (v_LET_NON_REC_18154_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_18155_n__8_p0_o));
                (v_LET_NON_REC_18154_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_18155_n__9_p0_o));
              }
              sisal_array_t v_LET_NON_REC_18154_n__3_p0_o = {0};
              double v_IF_array_dv_DOUBLE____18168_n__0_S2 = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_S2 = SISAL_CAST(double, v_LET_NON_REC_18154_n__1_p2_o));
              double v_IF_array_dv_DOUBLE____18168_n__0_SM2 = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_SM2 = SISAL_CAST(double, v_LET_NON_REC_18154_n__1_p1_o));
              sisal_array_t v_IF_array_dv_DOUBLE____18168_n__0_A = {0};
              (v_IF_array_dv_DOUBLE____18168_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_A));
              double v_IF_array_dv_DOUBLE____18168_n__0_EK = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_EK = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_EK));
              double v_IF_array_dv_DOUBLE____18168_n__0_EK1 = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_EK1 = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_EK1));
              double v_IF_array_dv_DOUBLE____18168_n__0_EK2 = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_EK2 = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_EK2));
              int32_t v_IF_array_dv_DOUBLE____18168_n__0_K = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_18154_n__0_K));
              int32_t v_IF_array_dv_DOUBLE____18168_n__0_N = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_18154_n__0_N));
              double v_IF_array_dv_DOUBLE____18168_n__0_OLD_EK = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_OLD_EK = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_OLD_EK));
              int32_t v_IF_array_dv_DOUBLE____18168_n__0_OLD_K = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_OLD_K = SISAL_CAST(int32_t, v_LET_NON_REC_18154_n__0_OLD_K));
              sisal_array_t v_IF_array_dv_DOUBLE____18168_n__0_OLD_Z = {0};
              (v_IF_array_dv_DOUBLE____18168_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_OLD_Z));
              double v_IF_array_dv_DOUBLE____18168_n__0_S = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_S = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_S));
              double v_IF_array_dv_DOUBLE____18168_n__0_SM = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_SM = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_SM));
              double v_IF_array_dv_DOUBLE____18168_n__0_WK = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_WK = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_WK));
              double v_IF_array_dv_DOUBLE____18168_n__0_WKM = 0;
              (v_IF_array_dv_DOUBLE____18168_n__0_WKM = SISAL_CAST(double, v_LET_NON_REC_18154_n__0_WKM));
              sisal_array_t v_IF_array_dv_DOUBLE____18168_n__0_Z = {0};
              (v_IF_array_dv_DOUBLE____18168_n__0_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_Z));
              sisal_array_t v_IF_array_dv_DOUBLE____18168_n__0_Z2 = {0};
              (v_IF_array_dv_DOUBLE____18168_n__0_Z2 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__0_Z2));
              sisal_array_t v_IF_array_dv_DOUBLE____18168_n__0_Z4 = {0};
              (v_IF_array_dv_DOUBLE____18168_n__0_Z4 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__1_p0_o));
              {
                double v_PREDICATE_18169_n__0_S2 = 0;
                double v_PREDICATE_18169_n__0_SM2 = 0;
                (v_PREDICATE_18169_n__0_S2 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_S2));
                (v_PREDICATE_18169_n__0_SM2 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_SM2));
                bool v_PREDICATE_18169_n__1_p0_o = 0;
                (v_PREDICATE_18169_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_18169_n__0_S2) >= SISAL_CAST(double, v_PREDICATE_18169_n__0_SM2))));
                if (v_PREDICATE_18169_n__1_p0_o) {
                  int32_t v_THEN_18180_n__0_OLD_K = 0;
                  double v_THEN_18180_n__0_WK = 0;
                  sisal_array_t v_THEN_18180_n__0_Z4 = {0};
                  (v_THEN_18180_n__0_Z4 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18168_n__0_Z4));
                  (v_THEN_18180_n__0_WK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_WK));
                  (v_THEN_18180_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18168_n__0_OLD_K));
                  sisal_array_t v_THEN_18180_n__1_p0_o = {0};
                  (v_THEN_18180_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_18180_n__0_Z4), ((int64_t)SISAL_CAST(int32_t, v_THEN_18180_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_THEN_18180_n__0_WK)))));
                  (v_LET_NON_REC_18154_n__3_p0_o = SISAL_CAST(sisal_array_t, v_THEN_18180_n__1_p0_o));
                }
                else {
                  sisal_array_t v_ELSE_18170_n__0_A = {0};
                  double v_ELSE_18170_n__0_EK = 0;
                  double v_ELSE_18170_n__0_EK1 = 0;
                  double v_ELSE_18170_n__0_EK2 = 0;
                  int32_t v_ELSE_18170_n__0_K = 0;
                  int32_t v_ELSE_18170_n__0_N = 0;
                  double v_ELSE_18170_n__0_OLD_EK = 0;
                  int32_t v_ELSE_18170_n__0_OLD_K = 0;
                  sisal_array_t v_ELSE_18170_n__0_OLD_Z = {0};
                  double v_ELSE_18170_n__0_S = 0;
                  double v_ELSE_18170_n__0_S2 = 0;
                  double v_ELSE_18170_n__0_SM = 0;
                  double v_ELSE_18170_n__0_SM2 = 0;
                  double v_ELSE_18170_n__0_WK = 0;
                  double v_ELSE_18170_n__0_WKM = 0;
                  sisal_array_t v_ELSE_18170_n__0_Z = {0};
                  sisal_array_t v_ELSE_18170_n__0_Z2 = {0};
                  sisal_array_t v_ELSE_18170_n__0_Z4 = {0};
                  (v_ELSE_18170_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18168_n__0_A));
                  (v_ELSE_18170_n__0_EK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_EK));
                  (v_ELSE_18170_n__0_EK1 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_EK1));
                  (v_ELSE_18170_n__0_EK2 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_EK2));
                  (v_ELSE_18170_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18168_n__0_K));
                  (v_ELSE_18170_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18168_n__0_N));
                  (v_ELSE_18170_n__0_OLD_EK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_OLD_EK));
                  (v_ELSE_18170_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____18168_n__0_OLD_K));
                  (v_ELSE_18170_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18168_n__0_OLD_Z));
                  (v_ELSE_18170_n__0_S = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_S));
                  (v_ELSE_18170_n__0_S2 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_S2));
                  (v_ELSE_18170_n__0_SM = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_SM));
                  (v_ELSE_18170_n__0_SM2 = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_SM2));
                  (v_ELSE_18170_n__0_WK = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_WK));
                  (v_ELSE_18170_n__0_WKM = SISAL_CAST(double, v_IF_array_dv_DOUBLE____18168_n__0_WKM));
                  (v_ELSE_18170_n__0_Z = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18168_n__0_Z));
                  (v_ELSE_18170_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18168_n__0_Z2));
                  (v_ELSE_18170_n__0_Z4 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____18168_n__0_Z4));
                  sisal_array_t v_ELSE_18170_n__1_p0_o = {0};
                  {
                    sisal_array_t v_LET_NON_REC_18171_n__0_A = {0};
                    double v_LET_NON_REC_18171_n__0_EK = 0;
                    double v_LET_NON_REC_18171_n__0_EK1 = 0;
                    double v_LET_NON_REC_18171_n__0_EK2 = 0;
                    sisal_array_t v_LET_NON_REC_18171_n__3_INIT = {0};
                    int32_t v_LET_NON_REC_18171_n__0_K = 0;
                    int32_t v_LET_NON_REC_18171_n__0_N = 0;
                    double v_LET_NON_REC_18171_n__0_OLD_EK = 0;
                    int32_t v_LET_NON_REC_18171_n__0_OLD_K = 0;
                    sisal_array_t v_LET_NON_REC_18171_n__0_OLD_Z = {0};
                    double v_LET_NON_REC_18171_n__0_S = 0;
                    double v_LET_NON_REC_18171_n__0_S2 = 0;
                    double v_LET_NON_REC_18171_n__0_SM = 0;
                    double v_LET_NON_REC_18171_n__0_SM2 = 0;
                    double v_LET_NON_REC_18171_n__1_T = 0;
                    double v_LET_NON_REC_18171_n__0_WK = 0;
                    double v_LET_NON_REC_18171_n__0_WK3 = 0;
                    double v_LET_NON_REC_18171_n__0_WKM = 0;
                    sisal_array_t v_LET_NON_REC_18171_n__0_Z = {0};
                    sisal_array_t v_LET_NON_REC_18171_n__0_Z2 = {0};
                    sisal_array_t v_LET_NON_REC_18171_n__0_Z4 = {0};
                    sisal_array_t v_LET_NON_REC_18171_n__6_Z7 = {0};
                    (v_LET_NON_REC_18171_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_18170_n__0_A));
                    (v_LET_NON_REC_18171_n__0_EK = SISAL_CAST(double, v_ELSE_18170_n__0_EK));
                    (v_LET_NON_REC_18171_n__0_EK1 = SISAL_CAST(double, v_ELSE_18170_n__0_EK1));
                    (v_LET_NON_REC_18171_n__0_EK2 = SISAL_CAST(double, v_ELSE_18170_n__0_EK2));
                    (v_LET_NON_REC_18171_n__0_K = SISAL_CAST(int32_t, v_ELSE_18170_n__0_K));
                    (v_LET_NON_REC_18171_n__0_N = SISAL_CAST(int32_t, v_ELSE_18170_n__0_N));
                    (v_LET_NON_REC_18171_n__0_OLD_EK = SISAL_CAST(double, v_ELSE_18170_n__0_OLD_EK));
                    (v_LET_NON_REC_18171_n__0_OLD_K = SISAL_CAST(int32_t, v_ELSE_18170_n__0_OLD_K));
                    (v_LET_NON_REC_18171_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_ELSE_18170_n__0_OLD_Z));
                    (v_LET_NON_REC_18171_n__0_S = SISAL_CAST(double, v_ELSE_18170_n__0_S));
                    (v_LET_NON_REC_18171_n__0_S2 = SISAL_CAST(double, v_ELSE_18170_n__0_S2));
                    (v_LET_NON_REC_18171_n__0_SM = SISAL_CAST(double, v_ELSE_18170_n__0_SM));
                    (v_LET_NON_REC_18171_n__0_SM2 = SISAL_CAST(double, v_ELSE_18170_n__0_SM2));
                    (v_LET_NON_REC_18171_n__0_WK = SISAL_CAST(double, v_ELSE_18170_n__0_WK));
                    (v_LET_NON_REC_18171_n__0_WKM = SISAL_CAST(double, v_ELSE_18170_n__0_WKM));
                    (v_LET_NON_REC_18171_n__0_Z = SISAL_CAST(sisal_array_t, v_ELSE_18170_n__0_Z));
                    (v_LET_NON_REC_18171_n__0_Z2 = SISAL_CAST(sisal_array_t, v_ELSE_18170_n__0_Z2));
                    (v_LET_NON_REC_18171_n__0_Z4 = SISAL_CAST(sisal_array_t, v_ELSE_18170_n__0_Z4));
                    (v_LET_NON_REC_18171_n__1_T = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_18171_n__0_WKM) - SISAL_CAST(double, v_LET_NON_REC_18171_n__0_WK))));
                    sisal_array_t v_LET_NON_REC_18171_n__2_p0_o = {0};
                    {
                      sisal_array_t v_FORALL_18172_n__0_A = v_LET_NON_REC_18171_n__0_A;
                      double v_FORALL_18172_n__0_EK = v_LET_NON_REC_18171_n__0_EK;
                      double v_FORALL_18172_n__0_EK1 = v_LET_NON_REC_18171_n__0_EK1;
                      double v_FORALL_18172_n__0_EK2 = v_LET_NON_REC_18171_n__0_EK2;
                      int32_t v_FORALL_18172_n__2_J;
                      int32_t v_FORALL_18172_n__0_K = v_LET_NON_REC_18171_n__0_K;
                      int32_t v_FORALL_18172_n__0_N = v_LET_NON_REC_18171_n__0_N;
                      double v_FORALL_18172_n__0_OLD_EK = v_LET_NON_REC_18171_n__0_OLD_EK;
                      int32_t v_FORALL_18172_n__0_OLD_K = v_LET_NON_REC_18171_n__0_OLD_K;
                      sisal_array_t v_FORALL_18172_n__0_OLD_Z = v_LET_NON_REC_18171_n__0_OLD_Z;
                      double v_FORALL_18172_n__0_S = v_LET_NON_REC_18171_n__0_S;
                      double v_FORALL_18172_n__0_S2 = v_LET_NON_REC_18171_n__0_S2;
                      double v_FORALL_18172_n__0_SM = v_LET_NON_REC_18171_n__0_SM;
                      double v_FORALL_18172_n__0_SM2 = v_LET_NON_REC_18171_n__0_SM2;
                      double v_FORALL_18172_n__0_T = v_LET_NON_REC_18171_n__1_T;
                      double v_FORALL_18172_n__0_WK = v_LET_NON_REC_18171_n__0_WK;
                      double v_FORALL_18172_n__0_WK3 = v_LET_NON_REC_18171_n__0_WKM;
                      double v_FORALL_18172_n__0_WKM = v_LET_NON_REC_18171_n__0_WKM;
                      sisal_array_t v_FORALL_18172_n__0_Z = v_LET_NON_REC_18171_n__0_Z;
                      sisal_array_t v_FORALL_18172_n__0_Z2 = v_LET_NON_REC_18171_n__0_Z2;
                      sisal_array_t v_FORALL_18172_n__0_Z4 = v_LET_NON_REC_18171_n__0_Z4;
                      double v_FORALL_18172_n__3___forall_body_0;
                      int32_t v_FORALL_18172_n__2___forall_lb_2_0;
                      int32_t v_FORALL_18172_n__2___forall_ub_2_0;
                      sisal_array_t v_GENERATOR_18174_n__0_A;
                      double v_GENERATOR_18174_n__0_EK;
                      double v_GENERATOR_18174_n__0_EK1;
                      double v_GENERATOR_18174_n__0_EK2;
                      int32_t v_GENERATOR_18174_n__2_J;
                      int32_t v_GENERATOR_18174_n__0_K;
                      int32_t v_GENERATOR_18174_n__0_N;
                      double v_GENERATOR_18174_n__0_OLD_EK;
                      int32_t v_GENERATOR_18174_n__0_OLD_K;
                      sisal_array_t v_GENERATOR_18174_n__0_OLD_Z;
                      double v_GENERATOR_18174_n__0_S;
                      double v_GENERATOR_18174_n__0_S2;
                      double v_GENERATOR_18174_n__0_SM;
                      double v_GENERATOR_18174_n__0_SM2;
                      double v_GENERATOR_18174_n__0_T;
                      double v_GENERATOR_18174_n__0_WK;
                      double v_GENERATOR_18174_n__0_WK3;
                      double v_GENERATOR_18174_n__0_WKM;
                      sisal_array_t v_GENERATOR_18174_n__0_Z;
                      sisal_array_t v_GENERATOR_18174_n__0_Z2;
                      sisal_array_t v_GENERATOR_18174_n__0_Z4;
                      int32_t v_GENERATOR_18174_n__2___forall_lb_2_0;
                      int32_t v_GENERATOR_18174_n__2___forall_ub_2_0;
                      sisal_array_t v_BODY_18175_n__0_A;
                      double v_BODY_18175_n__0_EK;
                      double v_BODY_18175_n__0_EK1;
                      double v_BODY_18175_n__0_EK2;
                      int32_t v_BODY_18175_n__0_J;
                      int32_t v_BODY_18175_n__0_K;
                      int32_t v_BODY_18175_n__0_N;
                      double v_BODY_18175_n__0_OLD_EK;
                      int32_t v_BODY_18175_n__0_OLD_K;
                      sisal_array_t v_BODY_18175_n__0_OLD_Z;
                      double v_BODY_18175_n__0_S;
                      double v_BODY_18175_n__0_S2;
                      double v_BODY_18175_n__0_SM;
                      double v_BODY_18175_n__0_SM2;
                      double v_BODY_18175_n__0_T;
                      double v_BODY_18175_n__0_WK;
                      double v_BODY_18175_n__0_WK3;
                      double v_BODY_18175_n__0_WKM;
                      sisal_array_t v_BODY_18175_n__0_Z;
                      sisal_array_t v_BODY_18175_n__0_Z2;
                      sisal_array_t v_BODY_18175_n__0_Z4;
                      int32_t v_BODY_18175_n__0___forall_lb_2_0;
                      int32_t v_BODY_18175_n__0___forall_ub_2_0;
                      (v_GENERATOR_18174_n__0_OLD_K = v_FORALL_18172_n__0_OLD_K);
                      (v_LET_NON_REC_18171_n__2_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_18174_n__0_OLD_K - 1) + 1)))));
                      (v_LET_NON_REC_18171_n__2_p0_o.dims[0] = ((v_GENERATOR_18174_n__0_OLD_K - 1) + 1));
                      (v_LET_NON_REC_18171_n__2_p0_o.lower_bound[0] = 1);
                      int32_t __g_18172 = 0;
                      (v_GENERATOR_18174_n__2___forall_lb_2_0 = 1);
                      (v_GENERATOR_18174_n__2___forall_ub_2_0 = v_GENERATOR_18174_n__0_OLD_K);
                      for ((v_GENERATOR_18174_n__2_J = 1); (v_GENERATOR_18174_n__2_J <= v_GENERATOR_18174_n__0_OLD_K); (v_GENERATOR_18174_n__2_J++)) {
                        (v_BODY_18175_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_18172_n__0_A));
                        (v_BODY_18175_n__0_EK = SISAL_CAST(double, v_FORALL_18172_n__0_EK));
                        (v_BODY_18175_n__0_EK1 = SISAL_CAST(double, v_FORALL_18172_n__0_EK1));
                        (v_BODY_18175_n__0_EK2 = SISAL_CAST(double, v_FORALL_18172_n__0_EK2));
                        (v_BODY_18175_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_18174_n__2_J));
                        (v_BODY_18175_n__0_K = SISAL_CAST(int32_t, v_FORALL_18172_n__0_K));
                        (v_BODY_18175_n__0_N = SISAL_CAST(int32_t, v_FORALL_18172_n__0_N));
                        (v_BODY_18175_n__0_OLD_EK = SISAL_CAST(double, v_FORALL_18172_n__0_OLD_EK));
                        (v_BODY_18175_n__0_OLD_K = SISAL_CAST(int32_t, v_FORALL_18172_n__0_OLD_K));
                        (v_BODY_18175_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_FORALL_18172_n__0_OLD_Z));
                        (v_BODY_18175_n__0_S = SISAL_CAST(double, v_FORALL_18172_n__0_S));
                        (v_BODY_18175_n__0_S2 = SISAL_CAST(double, v_FORALL_18172_n__0_S2));
                        (v_BODY_18175_n__0_SM = SISAL_CAST(double, v_FORALL_18172_n__0_SM));
                        (v_BODY_18175_n__0_SM2 = SISAL_CAST(double, v_FORALL_18172_n__0_SM2));
                        (v_BODY_18175_n__0_T = SISAL_CAST(double, v_FORALL_18172_n__0_T));
                        (v_BODY_18175_n__0_WK = SISAL_CAST(double, v_FORALL_18172_n__0_WK));
                        (v_BODY_18175_n__0_WK3 = SISAL_CAST(double, v_FORALL_18172_n__0_WK3));
                        (v_BODY_18175_n__0_WKM = SISAL_CAST(double, v_FORALL_18172_n__0_WKM));
                        (v_BODY_18175_n__0_Z = SISAL_CAST(sisal_array_t, v_FORALL_18172_n__0_Z));
                        (v_BODY_18175_n__0_Z2 = SISAL_CAST(sisal_array_t, v_FORALL_18172_n__0_Z2));
                        (v_BODY_18175_n__0_Z4 = SISAL_CAST(sisal_array_t, v_FORALL_18172_n__0_Z4));
                        (v_BODY_18175_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_18174_n__2___forall_lb_2_0));
                        (v_BODY_18175_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_18174_n__2___forall_ub_2_0));
                        double v_BODY_18175_n__1_p0_o = 0;
                        (v_BODY_18175_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18175_n__0_Z4).data)[(SISAL_CAST(int32_t, v_BODY_18175_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18175_n__0_Z4).lower_bound[0])]));
                        (((double *)v_LET_NON_REC_18171_n__2_p0_o.data)[__g_18172] = SISAL_CAST(double, v_BODY_18175_n__1_p0_o));
                        (__g_18172++);
                      }
                    }
                    sisal_array_t v_LET_NON_REC_18171_n__4_p0_o = {0};
                    {
                      sisal_array_t v_FORALL_18176_n__0_A = v_LET_NON_REC_18171_n__0_A;
                      double v_FORALL_18176_n__0_EK = v_LET_NON_REC_18171_n__0_EK;
                      double v_FORALL_18176_n__0_EK1 = v_LET_NON_REC_18171_n__0_EK1;
                      double v_FORALL_18176_n__0_EK2 = v_LET_NON_REC_18171_n__0_EK2;
                      sisal_array_t v_FORALL_18176_n__0_INIT = v_LET_NON_REC_18171_n__2_p0_o;
                      int32_t v_FORALL_18176_n__2_J;
                      int32_t v_FORALL_18176_n__0_K = v_LET_NON_REC_18171_n__0_K;
                      int32_t v_FORALL_18176_n__0_N = v_LET_NON_REC_18171_n__0_N;
                      double v_FORALL_18176_n__0_OLD_EK = v_LET_NON_REC_18171_n__0_OLD_EK;
                      int32_t v_FORALL_18176_n__0_OLD_K = v_LET_NON_REC_18171_n__0_OLD_K;
                      sisal_array_t v_FORALL_18176_n__0_OLD_Z = v_LET_NON_REC_18171_n__0_OLD_Z;
                      double v_FORALL_18176_n__0_S = v_LET_NON_REC_18171_n__0_S;
                      double v_FORALL_18176_n__0_S2 = v_LET_NON_REC_18171_n__0_S2;
                      double v_FORALL_18176_n__0_SM = v_LET_NON_REC_18171_n__0_SM;
                      double v_FORALL_18176_n__0_SM2 = v_LET_NON_REC_18171_n__0_SM2;
                      double v_FORALL_18176_n__0_T = v_LET_NON_REC_18171_n__1_T;
                      double v_FORALL_18176_n__0_WK = v_LET_NON_REC_18171_n__0_WK;
                      double v_FORALL_18176_n__0_WK3 = v_LET_NON_REC_18171_n__0_WKM;
                      double v_FORALL_18176_n__0_WKM = v_LET_NON_REC_18171_n__0_WKM;
                      sisal_array_t v_FORALL_18176_n__0_Z = v_LET_NON_REC_18171_n__0_Z;
                      sisal_array_t v_FORALL_18176_n__0_Z2 = v_LET_NON_REC_18171_n__0_Z2;
                      sisal_array_t v_FORALL_18176_n__0_Z4 = v_LET_NON_REC_18171_n__0_Z4;
                      double v_FORALL_18176_n__3___forall_body_0;
                      int32_t v_FORALL_18176_n__2___forall_lb_1_0;
                      int32_t v_FORALL_18176_n__2___forall_ub_1_0;
                      sisal_array_t v_GENERATOR_18178_n__0_A;
                      double v_GENERATOR_18178_n__0_EK;
                      double v_GENERATOR_18178_n__0_EK1;
                      double v_GENERATOR_18178_n__0_EK2;
                      sisal_array_t v_GENERATOR_18178_n__0_INIT;
                      int32_t v_GENERATOR_18178_n__1_J;
                      int32_t v_GENERATOR_18178_n__0_K;
                      int32_t v_GENERATOR_18178_n__0_N;
                      double v_GENERATOR_18178_n__0_OLD_EK;
                      int32_t v_GENERATOR_18178_n__0_OLD_K;
                      sisal_array_t v_GENERATOR_18178_n__0_OLD_Z;
                      double v_GENERATOR_18178_n__0_S;
                      double v_GENERATOR_18178_n__0_S2;
                      double v_GENERATOR_18178_n__0_SM;
                      double v_GENERATOR_18178_n__0_SM2;
                      double v_GENERATOR_18178_n__0_T;
                      double v_GENERATOR_18178_n__0_WK;
                      double v_GENERATOR_18178_n__0_WK3;
                      double v_GENERATOR_18178_n__0_WKM;
                      sisal_array_t v_GENERATOR_18178_n__0_Z;
                      sisal_array_t v_GENERATOR_18178_n__0_Z2;
                      sisal_array_t v_GENERATOR_18178_n__0_Z4;
                      int32_t v_GENERATOR_18178_n__1___forall_lb_1_0;
                      int32_t v_GENERATOR_18178_n__1___forall_ub_1_0;
                      sisal_array_t v_BODY_18179_n__0_A;
                      double v_BODY_18179_n__0_EK;
                      double v_BODY_18179_n__0_EK1;
                      double v_BODY_18179_n__0_EK2;
                      sisal_array_t v_BODY_18179_n__0_INIT;
                      int32_t v_BODY_18179_n__0_J;
                      int32_t v_BODY_18179_n__0_K;
                      int32_t v_BODY_18179_n__0_N;
                      double v_BODY_18179_n__0_OLD_EK;
                      int32_t v_BODY_18179_n__0_OLD_K;
                      sisal_array_t v_BODY_18179_n__0_OLD_Z;
                      double v_BODY_18179_n__0_S;
                      double v_BODY_18179_n__0_S2;
                      double v_BODY_18179_n__0_SM;
                      double v_BODY_18179_n__0_SM2;
                      double v_BODY_18179_n__0_T;
                      double v_BODY_18179_n__0_WK;
                      double v_BODY_18179_n__0_WK3;
                      double v_BODY_18179_n__0_WKM;
                      sisal_array_t v_BODY_18179_n__0_Z;
                      sisal_array_t v_BODY_18179_n__0_Z2;
                      sisal_array_t v_BODY_18179_n__0_Z4;
                      int32_t v_BODY_18179_n__0___forall_lb_1_0;
                      int32_t v_BODY_18179_n__0___forall_ub_1_0;
                      (v_GENERATOR_18178_n__0_K = v_FORALL_18176_n__0_K);
                      (v_GENERATOR_18178_n__0_N = v_FORALL_18176_n__0_N);
                      (v_LET_NON_REC_18171_n__4_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_18178_n__0_N - v_GENERATOR_18178_n__0_K) + 1)))));
                      (v_LET_NON_REC_18171_n__4_p0_o.dims[0] = ((v_GENERATOR_18178_n__0_N - v_GENERATOR_18178_n__0_K) + 1));
                      (v_LET_NON_REC_18171_n__4_p0_o.lower_bound[0] = v_GENERATOR_18178_n__0_K);
                      int32_t __g_18176 = 0;
                      (v_GENERATOR_18178_n__1___forall_lb_1_0 = v_GENERATOR_18178_n__0_K);
                      (v_GENERATOR_18178_n__1___forall_ub_1_0 = v_GENERATOR_18178_n__0_N);
                      for ((v_GENERATOR_18178_n__1_J = v_GENERATOR_18178_n__0_K); (v_GENERATOR_18178_n__1_J <= v_GENERATOR_18178_n__0_N); (v_GENERATOR_18178_n__1_J++)) {
                        (v_BODY_18179_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_18176_n__0_A));
                        (v_BODY_18179_n__0_EK = SISAL_CAST(double, v_FORALL_18176_n__0_EK));
                        (v_BODY_18179_n__0_EK1 = SISAL_CAST(double, v_FORALL_18176_n__0_EK1));
                        (v_BODY_18179_n__0_EK2 = SISAL_CAST(double, v_FORALL_18176_n__0_EK2));
                        (v_BODY_18179_n__0_INIT = SISAL_CAST(sisal_array_t, v_FORALL_18176_n__0_INIT));
                        (v_BODY_18179_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_18178_n__1_J));
                        (v_BODY_18179_n__0_K = SISAL_CAST(int32_t, v_FORALL_18176_n__0_K));
                        (v_BODY_18179_n__0_N = SISAL_CAST(int32_t, v_FORALL_18176_n__0_N));
                        (v_BODY_18179_n__0_OLD_EK = SISAL_CAST(double, v_FORALL_18176_n__0_OLD_EK));
                        (v_BODY_18179_n__0_OLD_K = SISAL_CAST(int32_t, v_FORALL_18176_n__0_OLD_K));
                        (v_BODY_18179_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_FORALL_18176_n__0_OLD_Z));
                        (v_BODY_18179_n__0_S = SISAL_CAST(double, v_FORALL_18176_n__0_S));
                        (v_BODY_18179_n__0_S2 = SISAL_CAST(double, v_FORALL_18176_n__0_S2));
                        (v_BODY_18179_n__0_SM = SISAL_CAST(double, v_FORALL_18176_n__0_SM));
                        (v_BODY_18179_n__0_SM2 = SISAL_CAST(double, v_FORALL_18176_n__0_SM2));
                        (v_BODY_18179_n__0_T = SISAL_CAST(double, v_FORALL_18176_n__0_T));
                        (v_BODY_18179_n__0_WK = SISAL_CAST(double, v_FORALL_18176_n__0_WK));
                        (v_BODY_18179_n__0_WK3 = SISAL_CAST(double, v_FORALL_18176_n__0_WK3));
                        (v_BODY_18179_n__0_WKM = SISAL_CAST(double, v_FORALL_18176_n__0_WKM));
                        (v_BODY_18179_n__0_Z = SISAL_CAST(sisal_array_t, v_FORALL_18176_n__0_Z));
                        (v_BODY_18179_n__0_Z2 = SISAL_CAST(sisal_array_t, v_FORALL_18176_n__0_Z2));
                        (v_BODY_18179_n__0_Z4 = SISAL_CAST(sisal_array_t, v_FORALL_18176_n__0_Z4));
                        (v_BODY_18179_n__0___forall_lb_1_0 = SISAL_CAST(int32_t, v_GENERATOR_18178_n__1___forall_lb_1_0));
                        (v_BODY_18179_n__0___forall_ub_1_0 = SISAL_CAST(int32_t, v_GENERATOR_18178_n__1___forall_ub_1_0));
                        double v_BODY_18179_n__1_p0_o = 0;
                        (v_BODY_18179_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18179_n__0_Z4).data)[(SISAL_CAST(int32_t, v_BODY_18179_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18179_n__0_Z4).lower_bound[0])]));
                        sisal_array_t v_BODY_18179_n__2_p0_o = {0};
                        (v_BODY_18179_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_18179_n__0_A), (SISAL_CAST(int32_t, v_BODY_18179_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_18179_n__0_A).lower_bound[0]))));
                        double v_BODY_18179_n__3_p0_o = 0;
                        (v_BODY_18179_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_18179_n__2_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_18179_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_18179_n__2_p0_o).lower_bound[0])]));
                        double v_BODY_18179_n__4_p0_o = 0;
                        (v_BODY_18179_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18179_n__0_T) * SISAL_CAST(double, v_BODY_18179_n__3_p0_o))));
                        double v_BODY_18179_n__5_p0_o = 0;
                        (v_BODY_18179_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_18179_n__1_p0_o) + SISAL_CAST(double, v_BODY_18179_n__4_p0_o))));
                        (((double *)v_LET_NON_REC_18171_n__4_p0_o.data)[__g_18176] = SISAL_CAST(double, v_BODY_18179_n__5_p0_o));
                        (__g_18176++);
                      }
                    }
                    (v_LET_NON_REC_18171_n__6_Z7 = SISAL_CAST(sisal_array_t, sisal_array_addh_arr(SISAL_CAST(sisal_array_t, v_LET_NON_REC_18171_n__2_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_18171_n__4_p0_o))));
                    sisal_array_t v_LET_NON_REC_18171_n__7_p0_o = {0};
                    (v_LET_NON_REC_18171_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_18171_n__6_Z7), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_18171_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_18171_n__0_WKM)))));
                    (v_ELSE_18170_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18171_n__7_p0_o));
                  }
                  (v_LET_NON_REC_18154_n__3_p0_o = SISAL_CAST(sisal_array_t, v_ELSE_18170_n__1_p0_o));
                }
              }
              (v_ELSE_18153_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18154_n__3_p0_o));
            }
            (v_BODY_18137_n__9_Z3 = SISAL_CAST(sisal_array_t, v_ELSE_18153_n__1_p0_o));
          }
        }
        bool v_BODY_18137_n__11_p0_o = 0;
        (v_BODY_18137_n__11_p0_o = SISAL_CAST(bool, false));
        (v_LoopB_18136_bodycap_n2_p0 = v_BODY_18137_n__2_K);
        (v_LoopB_18136_bodycap_n5_p0 = v_BODY_18137_n__5_EK2);
        (v_LoopB_18136_bodycap_n9_p0 = v_BODY_18137_n__9_Z3);
        (v_LoopB_18136_bodycap_n11_p0 = v_BODY_18137_n__11_p0_o);
        (v_LoopB_18136_n__5_MERGE_EK = v_LoopB_18136_bodycap_n5_p0);
        (v_LoopB_18136_n__6_MERGE_K = v_LoopB_18136_bodycap_n2_p0);
        (v_LoopB_18136_n__7_MERGE_Z = v_LoopB_18136_bodycap_n9_p0);
        (v_LoopB_18136_n__8_MERGE_OLD_EK = v_LoopB_18136_bodycap_n5_p0);
        (v_LoopB_18136_n__9_MERGE_OLD_K = v_LoopB_18136_bodycap_n2_p0);
        (v_LoopB_18136_n__10_MERGE_OLD_Z = v_LoopB_18136_bodycap_n9_p0);
        (v_LoopB_18136_n__11_MERGE_first = v_LoopB_18136_bodycap_n11_p0);
        (v_TEST_18183_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__0_A));
        (v_TEST_18183_n__0_EK = SISAL_CAST(double, v_LoopB_18136_n__5_MERGE_EK));
        (v_TEST_18183_n__0_K = SISAL_CAST(int32_t, v_LoopB_18136_n__6_MERGE_K));
        (v_TEST_18183_n__0_N = SISAL_CAST(int32_t, v_LoopB_18136_n__0_N));
        (v_TEST_18183_n__0_OLD_EK = SISAL_CAST(double, v_LoopB_18136_n__8_MERGE_OLD_EK));
        (v_TEST_18183_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_18136_n__9_MERGE_OLD_K));
        (v_TEST_18183_n__0_OLD_Z = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__10_MERGE_OLD_Z));
        (v_TEST_18183_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__7_MERGE_Z));
        (v_TEST_18183_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_18183_n__0_K) <= SISAL_CAST(int32_t, v_TEST_18183_n__0_N))));
      }
      sisal_array_t v_RETURNS_18182_n__0_p0_o = {0};
      (v_RETURNS_18182_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_18136_n__10_MERGE_OLD_Z));
      sisal_array_t v_RETURNS_18182_n__1_p0_o = {0};
      (v_RETURNS_18182_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_18182_n__0_p0_o)));
      (v_LET_NON_REC_18135_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_18182_n__1_p0_o));
    }
    (v_g8_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_18135_n__1_p0_o));
  }
  (v_g8_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g8_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g8_n__0_p0_i);
}

extern "C" struct FUNC_CALC_NEWZY1_results func_CALC_NEWZY1(int32_t N, sisal_array_t IPVT, sisal_array_t A, sisal_array_t Z) {
  sisal_array_t v_g9_n__0_A = {0};
  sisal_array_t v_g9_n__0_IPVT = {0};
  int32_t v_g9_n__0_N = 0;
  sisal_array_t v_g9_n__0_Z = {0};
  (v_g9_n__0_N = SISAL_CAST(int32_t, N));
  (v_g9_n__0_IPVT = SISAL_CAST(sisal_array_t, IPVT));
  (v_g9_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g9_n__0_Z = SISAL_CAST(sisal_array_t, Z));
  sisal_array_t v_g9_n__0_p0_i = {0};
  double v_g9_n__0_p1_i = 0;
  sisal_array_t v_g9_n__1_p0_o = {0};
  double v_g9_n__1_p1_o = 0;
  {
    int32_t v_LoopB_17122_n__5_MERGE_K = 0;
    sisal_array_t v_LoopB_17122_n__6_MERGE_NEW_Z = {0};
    double v_LoopB_17122_n__7_MERGE_YNORM = 0;
    int32_t v_LoopB_17122_n__8_MERGE_OLD_K = 0;
    sisal_array_t v_LoopB_17122_n__9_MERGE_OLD_NEW_Z = {0};
    double v_LoopB_17122_n__10_MERGE_OLD_YNORM = 0;
    bool v_LoopB_17122_n__11_MERGE_first = 0;
    int32_t v_LoopB_17122_bodycap_n2_p0 = 0;
    sisal_array_t v_LoopB_17122_bodycap_n12_p0 = {0};
    double v_LoopB_17122_bodycap_n12_p1 = 0;
    bool v_LoopB_17122_bodycap_n14_p0 = 0;
    sisal_array_t v_LoopB_17122_n__0_A = {0};
    (v_LoopB_17122_n__0_A = SISAL_CAST(sisal_array_t, v_g9_n__0_A));
    sisal_array_t v_LoopB_17122_n__0_IPVT = {0};
    (v_LoopB_17122_n__0_IPVT = SISAL_CAST(sisal_array_t, v_g9_n__0_IPVT));
    int32_t v_LoopB_17122_n__0_N = 0;
    (v_LoopB_17122_n__0_N = SISAL_CAST(int32_t, v_g9_n__0_N));
    sisal_array_t v_LoopB_17122_n__0_Z = {0};
    (v_LoopB_17122_n__0_Z = SISAL_CAST(sisal_array_t, v_g9_n__0_Z));
    sisal_array_t v_INIT_17134_n__0_A = {0};
    sisal_array_t v_INIT_17134_n__0_IPVT = {0};
    int32_t v_INIT_17134_n__1_K = 0;
    int32_t v_INIT_17134_n__0_N = 0;
    sisal_array_t v_INIT_17134_n__0_NEW_Z = {0};
    int32_t v_INIT_17134_n__1_OLD_K = 0;
    sisal_array_t v_INIT_17134_n__0_OLD_NEW_Z = {0};
    double v_INIT_17134_n__2_OLD_YNORM = 0;
    double v_INIT_17134_n__2_YNORM = 0;
    sisal_array_t v_INIT_17134_n__0_Z = {0};
    (v_INIT_17134_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_A));
    (v_INIT_17134_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_IPVT));
    (v_INIT_17134_n__0_N = SISAL_CAST(int32_t, v_LoopB_17122_n__0_N));
    (v_INIT_17134_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_Z));
    (v_INIT_17134_n__1_OLD_K = SISAL_CAST(int32_t, 1));
    (v_INIT_17134_n__2_YNORM = SISAL_CAST(double, 1.));
    bool v_INIT_17134_n__3_p0_o = 0;
    (v_INIT_17134_n__3_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_17122_n__5_MERGE_K = v_INIT_17134_n__1_OLD_K);
    (v_LoopB_17122_n__6_MERGE_NEW_Z = v_INIT_17134_n__0_Z);
    (v_LoopB_17122_n__7_MERGE_YNORM = v_INIT_17134_n__2_YNORM);
    (v_LoopB_17122_n__8_MERGE_OLD_K = v_INIT_17134_n__1_OLD_K);
    (v_LoopB_17122_n__9_MERGE_OLD_NEW_Z = v_INIT_17134_n__0_Z);
    (v_LoopB_17122_n__10_MERGE_OLD_YNORM = v_INIT_17134_n__2_YNORM);
    (v_LoopB_17122_n__11_MERGE_first = v_INIT_17134_n__3_p0_o);
    sisal_array_t v_TEST_17133_n__0_A = {0};
    sisal_array_t v_TEST_17133_n__0_IPVT = {0};
    int32_t v_TEST_17133_n__0_K = 0;
    int32_t v_TEST_17133_n__0_N = 0;
    sisal_array_t v_TEST_17133_n__0_NEW_Z = {0};
    int32_t v_TEST_17133_n__0_OLD_K = 0;
    sisal_array_t v_TEST_17133_n__0_OLD_NEW_Z = {0};
    double v_TEST_17133_n__0_OLD_YNORM = 0;
    double v_TEST_17133_n__0_YNORM = 0;
    sisal_array_t v_TEST_17133_n__0_Z = {0};
    (v_TEST_17133_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_A));
    (v_TEST_17133_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_IPVT));
    (v_TEST_17133_n__0_K = SISAL_CAST(int32_t, v_LoopB_17122_n__5_MERGE_K));
    (v_TEST_17133_n__0_N = SISAL_CAST(int32_t, v_LoopB_17122_n__0_N));
    (v_TEST_17133_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__6_MERGE_NEW_Z));
    (v_TEST_17133_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_17122_n__8_MERGE_OLD_K));
    (v_TEST_17133_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__9_MERGE_OLD_NEW_Z));
    (v_TEST_17133_n__0_OLD_YNORM = SISAL_CAST(double, v_LoopB_17122_n__10_MERGE_OLD_YNORM));
    (v_TEST_17133_n__0_YNORM = SISAL_CAST(double, v_LoopB_17122_n__7_MERGE_YNORM));
    (v_TEST_17133_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_Z));
    bool v_TEST_17133_n__1_p0_o = 0;
    (v_TEST_17133_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_17133_n__0_K) <= SISAL_CAST(int32_t, v_TEST_17133_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_17133_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_17122 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_17133_n__1_p0_o) {
      sisal_array_t v_BODY_17123_n__0_A = {0};
      sisal_array_t v_BODY_17123_n__0_IPVT = {0};
      int32_t v_BODY_17123_n__2_K = 0;
      int32_t v_BODY_17123_n__0_N = 0;
      sisal_array_t v_BODY_17123_n__12_NEW_Z = {0};
      int32_t v_BODY_17123_n__0_OLD_K = 0;
      sisal_array_t v_BODY_17123_n__0_OLD_NEW_Z = {0};
      double v_BODY_17123_n__0_OLD_YNORM = 0;
      sisal_array_t v_BODY_17123_n__9_TRANS_A = {0};
      double v_BODY_17123_n__12_YNORM = 0;
      sisal_array_t v_BODY_17123_n__0_Z = {0};
      sisal_array_t v_BODY_17123_n__8_Z2 = {0};
      sisal_array_t v_BODY_17123_n__10_Z3 = {0};
      (v_BODY_17123_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_A));
      (v_BODY_17123_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_IPVT));
      int32_t v_BODY_17123_n__0_p2_o = 0;
      (v_BODY_17123_n__0_p2_o = SISAL_CAST(int32_t, v_LoopB_17122_n__5_MERGE_K));
      (v_BODY_17123_n__0_N = SISAL_CAST(int32_t, v_LoopB_17122_n__0_N));
      sisal_array_t v_BODY_17123_n__0_p4_o = {0};
      (v_BODY_17123_n__0_p4_o = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__6_MERGE_NEW_Z));
      (v_BODY_17123_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_17122_n__8_MERGE_OLD_K));
      (v_BODY_17123_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__9_MERGE_OLD_NEW_Z));
      (v_BODY_17123_n__0_OLD_YNORM = SISAL_CAST(double, v_LoopB_17122_n__10_MERGE_OLD_YNORM));
      double v_BODY_17123_n__0_p8_o = 0;
      (v_BODY_17123_n__0_p8_o = SISAL_CAST(double, v_LoopB_17122_n__7_MERGE_YNORM));
      (v_BODY_17123_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_Z));
      int32_t v_BODY_17123_n__1_p0_o = 0;
      (v_BODY_17123_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_17123_n__2_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K) + SISAL_CAST(int32_t, v_BODY_17123_n__1_p0_o))));
      double v_BODY_17123_n__3_p0_o = 0;
      (v_BODY_17123_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_OLD_NEW_Z).lower_bound[0])]));
      int32_t v_BODY_17123_n__4_p0_o = 0;
      (v_BODY_17123_n__4_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_IPVT).data)[(SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_IPVT).lower_bound[0])]));
      sisal_array_t v_BODY_17123_n__5_p0_o = {0};
      (v_BODY_17123_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_OLD_NEW_Z), ((int64_t)SISAL_CAST(int32_t, v_BODY_17123_n__4_p0_o)), SISAL_CAST(double, SISAL_CAST(double, v_BODY_17123_n__3_p0_o)))));
      int32_t v_BODY_17123_n__6_p0_o = 0;
      (v_BODY_17123_n__6_p0_o = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_IPVT).data)[(SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_IPVT).lower_bound[0])]));
      double v_BODY_17123_n__7_p0_o = 0;
      (v_BODY_17123_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_BODY_17123_n__6_p0_o) - SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_OLD_NEW_Z).lower_bound[0])]));
      (v_BODY_17123_n__8_Z2 = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_BODY_17123_n__5_p0_o), ((int64_t)SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_BODY_17123_n__7_p0_o)))));
      (v_BODY_17123_n__9_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_BODY_17123_n__0_A))));
      int32_t v_IF_array_dv_DOUBLE____17124_n__0_OLD_K = 0;
      (v_IF_array_dv_DOUBLE____17124_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K));
      int32_t v_IF_array_dv_DOUBLE____17124_n__0_N = 0;
      (v_IF_array_dv_DOUBLE____17124_n__0_N = SISAL_CAST(int32_t, v_BODY_17123_n__0_N));
      sisal_array_t v_IF_array_dv_DOUBLE____17124_n__0_Z2 = {0};
      (v_IF_array_dv_DOUBLE____17124_n__0_Z2 = SISAL_CAST(sisal_array_t, v_BODY_17123_n__8_Z2));
      sisal_array_t v_IF_array_dv_DOUBLE____17124_n__0_TRANS_A = {0};
      (v_IF_array_dv_DOUBLE____17124_n__0_TRANS_A = SISAL_CAST(sisal_array_t, v_BODY_17123_n__9_TRANS_A));
      {
        int32_t v_PREDICATE_17125_n__0_N = 0;
        int32_t v_PREDICATE_17125_n__0_OLD_K = 0;
        (v_PREDICATE_17125_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____17124_n__0_OLD_K));
        (v_PREDICATE_17125_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____17124_n__0_N));
        bool v_PREDICATE_17125_n__1_p0_o = 0;
        (v_PREDICATE_17125_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_17125_n__0_OLD_K) < SISAL_CAST(int32_t, v_PREDICATE_17125_n__0_N))));
        if (v_PREDICATE_17125_n__1_p0_o) {
          int32_t v_THEN_17127_n__0_N = 0;
          int32_t v_THEN_17127_n__0_OLD_K = 0;
          sisal_array_t v_THEN_17127_n__0_TRANS_A = {0};
          sisal_array_t v_THEN_17127_n__0_Z2 = {0};
          (v_THEN_17127_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____17124_n__0_OLD_K));
          (v_THEN_17127_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____17124_n__0_N));
          (v_THEN_17127_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____17124_n__0_Z2));
          (v_THEN_17127_n__0_TRANS_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____17124_n__0_TRANS_A));
          int32_t v_THEN_17127_n__1_p0_o = 0;
          (v_THEN_17127_n__1_p0_o = SISAL_CAST(int32_t, 1));
          float v_THEN_17127_n__2_p0_o = 0;
          (v_THEN_17127_n__2_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K) + SISAL_CAST(int32_t, v_THEN_17127_n__1_p0_o))));
          float v_THEN_17127_n__3_p0_o = 0;
          (v_THEN_17127_n__3_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_THEN_17127_n__0_N) - SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K))));
          float v_THEN_17127_n__4_p0_o = 0;
          (v_THEN_17127_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_Z2).data)[(SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_Z2).lower_bound[0])]));
          float v_THEN_17127_n__5_p0_o = 0;
          (v_THEN_17127_n__5_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_TRANS_A).data)[(SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_TRANS_A).lower_bound[0])]));
          int32_t v_THEN_17127_n__6_p0_o = 0;
          (v_THEN_17127_n__6_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_THEN_17127_n__7_p0_o = 0;
          (v_THEN_17127_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K) + SISAL_CAST(int32_t, v_THEN_17127_n__6_p0_o))));
          int32_t v_THEN_17127_n__8_p0_o = 0;
          (v_THEN_17127_n__8_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_THEN_17127_n__0_N) - SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K))));
          double v_THEN_17127_n__9_p0_o = 0;
          (v_THEN_17127_n__9_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_Z2).data)[(SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_Z2).lower_bound[0])]));
          sisal_array_t v_THEN_17127_n__10_p0_o = {0};
          (v_THEN_17127_n__10_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_TRANS_A), (SISAL_CAST(int32_t, v_THEN_17127_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_TRANS_A).lower_bound[0]))));
          sisal_array_t v_THEN_17127_n__11_p0_o = {0};
          (v_THEN_17127_n__11_p0_o = SISAL_CAST(sisal_array_t, func_SAXPY(SISAL_CAST(int32_t, v_THEN_17127_n__7_p0_o), SISAL_CAST(int32_t, v_THEN_17127_n__8_p0_o), SISAL_CAST(double, v_THEN_17127_n__9_p0_o), SISAL_CAST(sisal_array_t, v_THEN_17127_n__10_p0_o), SISAL_CAST(sisal_array_t, v_THEN_17127_n__0_Z2))));
          (v_BODY_17123_n__10_Z3 = SISAL_CAST(sisal_array_t, v_THEN_17127_n__11_p0_o));
        }
        else {
          sisal_array_t v_ELSE_17126_n__0_Z2 = {0};
          (v_ELSE_17126_n__0_Z2 = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____17124_n__0_Z2));
          (v_BODY_17123_n__10_Z3 = SISAL_CAST(sisal_array_t, v_ELSE_17126_n__0_Z2));
        }
      }
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_Z3 = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_Z3 = SISAL_CAST(sisal_array_t, v_BODY_17123_n__10_Z3));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_K = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_17123_n__0_OLD_K));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_N = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_N = SISAL_CAST(int32_t, v_BODY_17123_n__0_N));
      double v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_YNORM = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_YNORM = SISAL_CAST(double, v_BODY_17123_n__0_OLD_YNORM));
      {
        int32_t v_PREDICATE_17129_n__0_OLD_K = 0;
        sisal_array_t v_PREDICATE_17129_n__0_Z3 = {0};
        (v_PREDICATE_17129_n__0_Z3 = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_Z3));
        (v_PREDICATE_17129_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_K));
        float v_PREDICATE_17129_n__1_p0_o = 0;
        (v_PREDICATE_17129_n__1_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_PREDICATE_17129_n__0_Z3).data)[(SISAL_CAST(int32_t, v_PREDICATE_17129_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_17129_n__0_Z3).lower_bound[0])]));
        double v_PREDICATE_17129_n__2_p0_o = 0;
        (v_PREDICATE_17129_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_17129_n__0_Z3).data)[(SISAL_CAST(int32_t, v_PREDICATE_17129_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_17129_n__0_Z3).lower_bound[0])]));
        double v_PREDICATE_17129_n__3_p0_o = 0;
        (v_PREDICATE_17129_n__3_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_17129_n__2_p0_o))));
        double v_PREDICATE_17129_n__4_p0_o = 0;
        (v_PREDICATE_17129_n__4_p0_o = SISAL_CAST(double, 1.));
        bool v_PREDICATE_17129_n__5_p0_o = 0;
        (v_PREDICATE_17129_n__5_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_17129_n__3_p0_o) <= SISAL_CAST(double, v_PREDICATE_17129_n__4_p0_o))));
        if (v_PREDICATE_17129_n__5_p0_o) {
          double v_THEN_17131_n__0_OLD_YNORM = 0;
          sisal_array_t v_THEN_17131_n__0_Z3 = {0};
          (v_THEN_17131_n__0_Z3 = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_Z3));
          (v_THEN_17131_n__0_OLD_YNORM = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_YNORM));
          (v_BODY_17123_n__12_NEW_Z = SISAL_CAST(sisal_array_t, v_THEN_17131_n__0_Z3));
          (v_BODY_17123_n__12_YNORM = SISAL_CAST(double, v_THEN_17131_n__0_OLD_YNORM));
        }
        else {
          int32_t v_ELSE_17130_n__0_N = 0;
          int32_t v_ELSE_17130_n__0_OLD_K = 0;
          double v_ELSE_17130_n__0_OLD_YNORM = 0;
          sisal_array_t v_ELSE_17130_n__0_Z3 = {0};
          (v_ELSE_17130_n__0_N = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_N));
          (v_ELSE_17130_n__0_Z3 = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_Z3));
          (v_ELSE_17130_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_K));
          (v_ELSE_17130_n__0_OLD_YNORM = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____17128_n__0_OLD_YNORM));
          int32_t v_ELSE_17130_n__1_p0_o = 0;
          (v_ELSE_17130_n__1_p0_o = SISAL_CAST(int32_t, 1));
          double v_ELSE_17130_n__2_p0_o = 0;
          (v_ELSE_17130_n__2_p0_o = SISAL_CAST(double, 1.));
          double v_ELSE_17130_n__3_p0_o = 0;
          (v_ELSE_17130_n__3_p0_o = SISAL_CAST(double, 1.));
          float v_ELSE_17130_n__4_p0_o = 0;
          (v_ELSE_17130_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).data)[(SISAL_CAST(int32_t, v_ELSE_17130_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).lower_bound[0])]));
          double v_ELSE_17130_n__5_p0_o = 0;
          (v_ELSE_17130_n__5_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).data)[(SISAL_CAST(int32_t, v_ELSE_17130_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).lower_bound[0])]));
          double v_ELSE_17130_n__6_p0_o = 0;
          (v_ELSE_17130_n__6_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_17130_n__5_p0_o))));
          float v_ELSE_17130_n__7_p0_o = 0;
          (v_ELSE_17130_n__7_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_ELSE_17130_n__3_p0_o) / SISAL_CAST(double, v_ELSE_17130_n__6_p0_o))));
          int32_t v_ELSE_17130_n__8_p0_o = 0;
          (v_ELSE_17130_n__8_p0_o = SISAL_CAST(int32_t, 1));
          double v_ELSE_17130_n__9_p0_o = 0;
          (v_ELSE_17130_n__9_p0_o = SISAL_CAST(double, 1.));
          double v_ELSE_17130_n__10_p0_o = 0;
          (v_ELSE_17130_n__10_p0_o = SISAL_CAST(double, 1.));
          float v_ELSE_17130_n__11_p0_o = 0;
          (v_ELSE_17130_n__11_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).data)[(SISAL_CAST(int32_t, v_ELSE_17130_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).lower_bound[0])]));
          double v_ELSE_17130_n__12_p0_o = 0;
          (v_ELSE_17130_n__12_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).data)[(SISAL_CAST(int32_t, v_ELSE_17130_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).lower_bound[0])]));
          double v_ELSE_17130_n__13_p0_o = 0;
          (v_ELSE_17130_n__13_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_17130_n__12_p0_o))));
          double v_ELSE_17130_n__14_p0_o = 0;
          (v_ELSE_17130_n__14_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_17130_n__10_p0_o) / SISAL_CAST(double, v_ELSE_17130_n__13_p0_o))));
          sisal_array_t v_ELSE_17130_n__15_p0_o = {0};
          (v_ELSE_17130_n__15_p0_o = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_ELSE_17130_n__8_p0_o), SISAL_CAST(int32_t, v_ELSE_17130_n__0_N), SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3), SISAL_CAST(double, v_ELSE_17130_n__14_p0_o))));
          double v_ELSE_17130_n__16_p0_o = 0;
          (v_ELSE_17130_n__16_p0_o = SISAL_CAST(double, 1.));
          double v_ELSE_17130_n__17_p0_o = 0;
          (v_ELSE_17130_n__17_p0_o = SISAL_CAST(double, 1.));
          float v_ELSE_17130_n__18_p0_o = 0;
          (v_ELSE_17130_n__18_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).data)[(SISAL_CAST(int32_t, v_ELSE_17130_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).lower_bound[0])]));
          double v_ELSE_17130_n__19_p0_o = 0;
          (v_ELSE_17130_n__19_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).data)[(SISAL_CAST(int32_t, v_ELSE_17130_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_17130_n__0_Z3).lower_bound[0])]));
          double v_ELSE_17130_n__20_p0_o = 0;
          (v_ELSE_17130_n__20_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_ELSE_17130_n__19_p0_o))));
          double v_ELSE_17130_n__21_p0_o = 0;
          (v_ELSE_17130_n__21_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_17130_n__17_p0_o) / SISAL_CAST(double, v_ELSE_17130_n__20_p0_o))));
          double v_ELSE_17130_n__23_p0_o = 0;
          (v_ELSE_17130_n__23_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_17130_n__21_p0_o) * SISAL_CAST(double, v_ELSE_17130_n__0_OLD_YNORM))));
          (v_BODY_17123_n__12_NEW_Z = SISAL_CAST(sisal_array_t, v_ELSE_17130_n__15_p0_o));
          (v_BODY_17123_n__12_YNORM = SISAL_CAST(double, v_ELSE_17130_n__23_p0_o));
        }
      }
      bool v_BODY_17123_n__14_p0_o = 0;
      (v_BODY_17123_n__14_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_17122_bodycap_n2_p0 = v_BODY_17123_n__2_K);
      (v_LoopB_17122_bodycap_n12_p0 = v_BODY_17123_n__12_NEW_Z);
      (v_LoopB_17122_bodycap_n12_p1 = v_BODY_17123_n__12_YNORM);
      (v_LoopB_17122_bodycap_n14_p0 = v_BODY_17123_n__14_p0_o);
      (v_LoopB_17122_n__5_MERGE_K = v_LoopB_17122_bodycap_n2_p0);
      (v_LoopB_17122_n__6_MERGE_NEW_Z = v_LoopB_17122_bodycap_n12_p0);
      (v_LoopB_17122_n__7_MERGE_YNORM = v_LoopB_17122_bodycap_n12_p1);
      (v_LoopB_17122_n__8_MERGE_OLD_K = v_LoopB_17122_bodycap_n2_p0);
      (v_LoopB_17122_n__9_MERGE_OLD_NEW_Z = v_LoopB_17122_bodycap_n12_p0);
      (v_LoopB_17122_n__10_MERGE_OLD_YNORM = v_LoopB_17122_bodycap_n12_p1);
      (v_LoopB_17122_n__11_MERGE_first = v_LoopB_17122_bodycap_n14_p0);
      (v_TEST_17133_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_A));
      (v_TEST_17133_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_IPVT));
      (v_TEST_17133_n__0_K = SISAL_CAST(int32_t, v_LoopB_17122_n__5_MERGE_K));
      (v_TEST_17133_n__0_N = SISAL_CAST(int32_t, v_LoopB_17122_n__0_N));
      (v_TEST_17133_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__6_MERGE_NEW_Z));
      (v_TEST_17133_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_17122_n__8_MERGE_OLD_K));
      (v_TEST_17133_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__9_MERGE_OLD_NEW_Z));
      (v_TEST_17133_n__0_OLD_YNORM = SISAL_CAST(double, v_LoopB_17122_n__10_MERGE_OLD_YNORM));
      (v_TEST_17133_n__0_YNORM = SISAL_CAST(double, v_LoopB_17122_n__7_MERGE_YNORM));
      (v_TEST_17133_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__0_Z));
      (v_TEST_17133_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_17133_n__0_K) <= SISAL_CAST(int32_t, v_TEST_17133_n__0_N))));
    }
    sisal_array_t v_RETURNS_17132_n__0_p0_o = {0};
    double v_RETURNS_17132_n__0_p1_o = 0;
    (v_RETURNS_17132_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_17122_n__9_MERGE_OLD_NEW_Z));
    (v_RETURNS_17132_n__0_p1_o = SISAL_CAST(double, v_LoopB_17122_n__10_MERGE_OLD_YNORM));
    sisal_array_t v_RETURNS_17132_n__1_p0_o = {0};
    (v_RETURNS_17132_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_17132_n__0_p0_o)));
    double v_RETURNS_17132_n__2_p0_o = 0;
    (v_RETURNS_17132_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(double, v_RETURNS_17132_n__0_p1_o)));
    (v_g9_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_17132_n__1_p0_o));
    (v_g9_n__1_p1_o = SISAL_CAST(double, v_RETURNS_17132_n__2_p0_o));
  }
  (v_g9_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g9_n__1_p0_o));
  (v_g9_n__0_p1_i = SISAL_CAST(double, v_g9_n__1_p1_o));
  struct FUNC_CALC_NEWZY1_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g9_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(double, v_g9_n__0_p1_i));
  return __res_obj;
}

extern "C" struct FUNC_CALC_NEWZY2_results func_CALC_NEWZY2(int32_t N, sisal_array_t A, sisal_array_t Z, double YNORM) {
  sisal_array_t v_g10_n__0_A = {0};
  int32_t v_g10_n__0_N = 0;
  double v_g10_n__0_YNORM = 0;
  sisal_array_t v_g10_n__0_Z = {0};
  (v_g10_n__0_N = SISAL_CAST(int32_t, N));
  (v_g10_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g10_n__0_Z = SISAL_CAST(sisal_array_t, Z));
  (v_g10_n__0_YNORM = SISAL_CAST(double, YNORM));
  sisal_array_t v_g10_n__0_p0_i = {0};
  double v_g10_n__0_p1_i = 0;
  sisal_array_t v_g10_n__1_p0_o = {0};
  double v_g10_n__1_p1_o = 0;
  {
    int32_t v_LoopB_16097_n__5_MERGE_KB = 0;
    double v_LoopB_16097_n__6_MERGE_NEW_Y = 0;
    sisal_array_t v_LoopB_16097_n__7_MERGE_NEW_Z = {0};
    int32_t v_LoopB_16097_n__8_MERGE_OLD_KB = 0;
    double v_LoopB_16097_n__9_MERGE_OLD_NEW_Y = 0;
    sisal_array_t v_LoopB_16097_n__10_MERGE_OLD_NEW_Z = {0};
    bool v_LoopB_16097_n__11_MERGE_first = 0;
    int32_t v_LoopB_16097_bodycap_n2_p0 = 0;
    double v_LoopB_16097_bodycap_n6_p1 = 0;
    sisal_array_t v_LoopB_16097_bodycap_n10_p0 = {0};
    bool v_LoopB_16097_bodycap_n12_p0 = 0;
    sisal_array_t v_LoopB_16097_n__0_A = {0};
    (v_LoopB_16097_n__0_A = SISAL_CAST(sisal_array_t, v_g10_n__0_A));
    int32_t v_LoopB_16097_n__0_N = 0;
    (v_LoopB_16097_n__0_N = SISAL_CAST(int32_t, v_g10_n__0_N));
    double v_LoopB_16097_n__0_YNORM = 0;
    (v_LoopB_16097_n__0_YNORM = SISAL_CAST(double, v_g10_n__0_YNORM));
    sisal_array_t v_LoopB_16097_n__0_Z = {0};
    (v_LoopB_16097_n__0_Z = SISAL_CAST(sisal_array_t, v_g10_n__0_Z));
    sisal_array_t v_INIT_16121_n__0_A = {0};
    int32_t v_INIT_16121_n__1_KB = 0;
    int32_t v_INIT_16121_n__0_N = 0;
    double v_INIT_16121_n__0_NEW_Y = 0;
    sisal_array_t v_INIT_16121_n__0_NEW_Z = {0};
    int32_t v_INIT_16121_n__1_OLD_KB = 0;
    double v_INIT_16121_n__0_OLD_NEW_Y = 0;
    sisal_array_t v_INIT_16121_n__0_OLD_NEW_Z = {0};
    double v_INIT_16121_n__0_YNORM = 0;
    sisal_array_t v_INIT_16121_n__0_Z = {0};
    (v_INIT_16121_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_A));
    (v_INIT_16121_n__0_N = SISAL_CAST(int32_t, v_LoopB_16097_n__0_N));
    (v_INIT_16121_n__0_YNORM = SISAL_CAST(double, v_LoopB_16097_n__0_YNORM));
    (v_INIT_16121_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_Z));
    (v_INIT_16121_n__1_OLD_KB = SISAL_CAST(int32_t, 1));
    bool v_INIT_16121_n__2_p0_o = 0;
    (v_INIT_16121_n__2_p0_o = SISAL_CAST(bool, true));
    (v_LoopB_16097_n__5_MERGE_KB = v_INIT_16121_n__1_OLD_KB);
    (v_LoopB_16097_n__6_MERGE_NEW_Y = v_INIT_16121_n__0_YNORM);
    (v_LoopB_16097_n__7_MERGE_NEW_Z = v_INIT_16121_n__0_Z);
    (v_LoopB_16097_n__8_MERGE_OLD_KB = v_INIT_16121_n__1_OLD_KB);
    (v_LoopB_16097_n__9_MERGE_OLD_NEW_Y = v_INIT_16121_n__0_YNORM);
    (v_LoopB_16097_n__10_MERGE_OLD_NEW_Z = v_INIT_16121_n__0_Z);
    (v_LoopB_16097_n__11_MERGE_first = v_INIT_16121_n__2_p0_o);
    sisal_array_t v_TEST_16120_n__0_A = {0};
    int32_t v_TEST_16120_n__0_KB = 0;
    int32_t v_TEST_16120_n__0_N = 0;
    double v_TEST_16120_n__0_NEW_Y = 0;
    sisal_array_t v_TEST_16120_n__0_NEW_Z = {0};
    int32_t v_TEST_16120_n__0_OLD_KB = 0;
    double v_TEST_16120_n__0_OLD_NEW_Y = 0;
    sisal_array_t v_TEST_16120_n__0_OLD_NEW_Z = {0};
    double v_TEST_16120_n__0_YNORM = 0;
    sisal_array_t v_TEST_16120_n__0_Z = {0};
    (v_TEST_16120_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_A));
    (v_TEST_16120_n__0_KB = SISAL_CAST(int32_t, v_LoopB_16097_n__5_MERGE_KB));
    (v_TEST_16120_n__0_N = SISAL_CAST(int32_t, v_LoopB_16097_n__0_N));
    (v_TEST_16120_n__0_NEW_Y = SISAL_CAST(double, v_LoopB_16097_n__6_MERGE_NEW_Y));
    (v_TEST_16120_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__7_MERGE_NEW_Z));
    (v_TEST_16120_n__0_OLD_KB = SISAL_CAST(int32_t, v_LoopB_16097_n__8_MERGE_OLD_KB));
    (v_TEST_16120_n__0_OLD_NEW_Y = SISAL_CAST(double, v_LoopB_16097_n__9_MERGE_OLD_NEW_Y));
    (v_TEST_16120_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__10_MERGE_OLD_NEW_Z));
    (v_TEST_16120_n__0_YNORM = SISAL_CAST(double, v_LoopB_16097_n__0_YNORM));
    (v_TEST_16120_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_Z));
    bool v_TEST_16120_n__1_p0_o = 0;
    (v_TEST_16120_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_16120_n__0_KB) <= SISAL_CAST(int32_t, v_TEST_16120_n__0_N))));
    #ifdef SISAL_TRAP_ZERO_TRIP
    if ((!v_TEST_16120_n__1_p0_o)) {
      fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_16097 executed 0 times (guard false on entry)\n");
      exit(1);
    }
    #endif
    while (v_TEST_16120_n__1_p0_o) {
      sisal_array_t v_BODY_16098_n__0_A = {0};
      int32_t v_BODY_16098_n__5_K = 0;
      int32_t v_BODY_16098_n__2_KB = 0;
      int32_t v_BODY_16098_n__0_N = 0;
      double v_BODY_16098_n__6_NEW_Y = 0;
      sisal_array_t v_BODY_16098_n__10_NEW_Z = {0};
      int32_t v_BODY_16098_n__0_OLD_KB = 0;
      double v_BODY_16098_n__0_OLD_NEW_Y = 0;
      sisal_array_t v_BODY_16098_n__0_OLD_NEW_Z = {0};
      double v_BODY_16098_n__0_YNORM = 0;
      sisal_array_t v_BODY_16098_n__0_Z = {0};
      sisal_array_t v_BODY_16098_n__6_ZTEMP = {0};
      sisal_array_t v_BODY_16098_n__8_ZTEMP2 = {0};
      double v_BODY_16098_n__0_p3_o = 0;
      sisal_array_t v_BODY_16098_n__0_p4_o = {0};
      (v_BODY_16098_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_A));
      int32_t v_BODY_16098_n__0_p1_o = 0;
      (v_BODY_16098_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_16097_n__5_MERGE_KB));
      (v_BODY_16098_n__0_N = SISAL_CAST(int32_t, v_LoopB_16097_n__0_N));
      (v_BODY_16098_n__0_p3_o = SISAL_CAST(double, v_LoopB_16097_n__6_MERGE_NEW_Y));
      (v_BODY_16098_n__0_p4_o = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__7_MERGE_NEW_Z));
      (v_BODY_16098_n__0_OLD_KB = SISAL_CAST(int32_t, v_LoopB_16097_n__8_MERGE_OLD_KB));
      (v_BODY_16098_n__0_OLD_NEW_Y = SISAL_CAST(double, v_LoopB_16097_n__9_MERGE_OLD_NEW_Y));
      (v_BODY_16098_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__10_MERGE_OLD_NEW_Z));
      (v_BODY_16098_n__0_YNORM = SISAL_CAST(double, v_LoopB_16097_n__0_YNORM));
      (v_BODY_16098_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_Z));
      int32_t v_BODY_16098_n__1_p0_o = 0;
      (v_BODY_16098_n__1_p0_o = SISAL_CAST(int32_t, 1));
      (v_BODY_16098_n__2_KB = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_16098_n__0_OLD_KB) + SISAL_CAST(int32_t, v_BODY_16098_n__1_p0_o))));
      int32_t v_BODY_16098_n__3_p0_o = 0;
      (v_BODY_16098_n__3_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_BODY_16098_n__4_p0_o = 0;
      (v_BODY_16098_n__4_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_16098_n__0_N) + SISAL_CAST(int32_t, v_BODY_16098_n__3_p0_o))));
      (v_BODY_16098_n__5_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_16098_n__4_p0_o) - SISAL_CAST(int32_t, v_BODY_16098_n__0_OLD_KB))));
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Z = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_OLD_NEW_Z));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_K = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_K = SISAL_CAST(int32_t, v_BODY_16098_n__5_K));
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_A = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_A));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_KB = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_KB = SISAL_CAST(int32_t, v_BODY_16098_n__2_KB));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_N = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_N = SISAL_CAST(int32_t, v_BODY_16098_n__0_N));
      double v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_NEW_Y = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_NEW_Y = SISAL_CAST(double, v_BODY_16098_n__0_p3_o));
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_NEW_Z = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_p4_o));
      int32_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_KB = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_KB = SISAL_CAST(int32_t, v_BODY_16098_n__0_OLD_KB));
      double v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Y = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Y = SISAL_CAST(double, v_BODY_16098_n__0_OLD_NEW_Y));
      double v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_YNORM = 0;
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_YNORM = SISAL_CAST(double, v_BODY_16098_n__0_YNORM));
      sisal_array_t v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_Z = {0};
      (v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_Z = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_Z));
      {
        sisal_array_t v_PREDICATE_16100_n__0_A = {0};
        int32_t v_PREDICATE_16100_n__0_K = 0;
        sisal_array_t v_PREDICATE_16100_n__0_OLD_NEW_Z = {0};
        (v_PREDICATE_16100_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Z));
        (v_PREDICATE_16100_n__0_K = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_K));
        (v_PREDICATE_16100_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_A));
        float v_PREDICATE_16100_n__1_p0_o = 0;
        (v_PREDICATE_16100_n__1_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_PREDICATE_16100_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_OLD_NEW_Z).lower_bound[0])]));
        double v_PREDICATE_16100_n__2_p0_o = 0;
        (v_PREDICATE_16100_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_PREDICATE_16100_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_OLD_NEW_Z).lower_bound[0])]));
        double v_PREDICATE_16100_n__3_p0_o = 0;
        (v_PREDICATE_16100_n__3_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_16100_n__2_p0_o))));
        sisal_array_t v_PREDICATE_16100_n__4_p0_o = {0};
        (v_PREDICATE_16100_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_16100_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_A).lower_bound[0]))));
        float v_PREDICATE_16100_n__5_p0_o = 0;
        (v_PREDICATE_16100_n__5_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__4_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_16100_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__4_p0_o).lower_bound[0])]));
        sisal_array_t v_PREDICATE_16100_n__6_p0_o = {0};
        (v_PREDICATE_16100_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_16100_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__0_A).lower_bound[0]))));
        double v_PREDICATE_16100_n__7_p0_o = 0;
        (v_PREDICATE_16100_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__6_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_16100_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16100_n__6_p0_o).lower_bound[0])]));
        double v_PREDICATE_16100_n__8_p0_o = 0;
        (v_PREDICATE_16100_n__8_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_PREDICATE_16100_n__7_p0_o))));
        bool v_PREDICATE_16100_n__9_p0_o = 0;
        (v_PREDICATE_16100_n__9_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_16100_n__3_p0_o) <= SISAL_CAST(double, v_PREDICATE_16100_n__8_p0_o))));
        if (v_PREDICATE_16100_n__9_p0_o) {
          double v_THEN_16107_n__0_OLD_NEW_Y = 0;
          sisal_array_t v_THEN_16107_n__0_OLD_NEW_Z = {0};
          (v_THEN_16107_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Z));
          (v_THEN_16107_n__0_OLD_NEW_Y = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Y));
          (v_BODY_16098_n__6_ZTEMP = SISAL_CAST(sisal_array_t, v_THEN_16107_n__0_OLD_NEW_Z));
          (v_BODY_16098_n__6_NEW_Y = SISAL_CAST(double, v_THEN_16107_n__0_OLD_NEW_Y));
        }
        else {
          sisal_array_t v_ELSE_16101_n__0_A = {0};
          int32_t v_ELSE_16101_n__0_K = 0;
          int32_t v_ELSE_16101_n__0_KB = 0;
          int32_t v_ELSE_16101_n__0_N = 0;
          double v_ELSE_16101_n__0_NEW_Y = 0;
          sisal_array_t v_ELSE_16101_n__0_NEW_Z = {0};
          int32_t v_ELSE_16101_n__0_OLD_KB = 0;
          double v_ELSE_16101_n__0_OLD_NEW_Y = 0;
          sisal_array_t v_ELSE_16101_n__0_OLD_NEW_Z = {0};
          double v_ELSE_16101_n__0_YNORM = 0;
          sisal_array_t v_ELSE_16101_n__0_Z = {0};
          (v_ELSE_16101_n__0_A = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_A));
          (v_ELSE_16101_n__0_K = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_K));
          (v_ELSE_16101_n__0_KB = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_KB));
          (v_ELSE_16101_n__0_N = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_N));
          (v_ELSE_16101_n__0_NEW_Y = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_NEW_Y));
          (v_ELSE_16101_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_NEW_Z));
          (v_ELSE_16101_n__0_OLD_KB = SISAL_CAST(int32_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_KB));
          (v_ELSE_16101_n__0_OLD_NEW_Y = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Y));
          (v_ELSE_16101_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_OLD_NEW_Z));
          (v_ELSE_16101_n__0_YNORM = SISAL_CAST(double, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_YNORM));
          (v_ELSE_16101_n__0_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE__array_dv_DOUBLE____16099_n__0_Z));
          sisal_array_t v_ELSE_16101_n__1_p0_o = {0};
          double v_ELSE_16101_n__1_p1_o = 0;
          {
            sisal_array_t v_LET_NON_REC_16102_n__0_A = {0};
            double v_LET_NON_REC_16102_n__2_GARB = 0;
            int32_t v_LET_NON_REC_16102_n__0_K = 0;
            int32_t v_LET_NON_REC_16102_n__0_KB = 0;
            int32_t v_LET_NON_REC_16102_n__0_N = 0;
            double v_LET_NON_REC_16102_n__0_NEW_Y = 0;
            sisal_array_t v_LET_NON_REC_16102_n__0_NEW_Z = {0};
            int32_t v_LET_NON_REC_16102_n__0_OLD_KB = 0;
            double v_LET_NON_REC_16102_n__0_OLD_NEW_Y = 0;
            sisal_array_t v_LET_NON_REC_16102_n__0_OLD_NEW_Z = {0};
            double v_LET_NON_REC_16102_n__16_S = 0;
            double v_LET_NON_REC_16102_n__0_YNORM = 0;
            sisal_array_t v_LET_NON_REC_16102_n__0_Z = {0};
            (v_LET_NON_REC_16102_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_16101_n__0_A));
            (v_LET_NON_REC_16102_n__0_K = SISAL_CAST(int32_t, v_ELSE_16101_n__0_K));
            (v_LET_NON_REC_16102_n__0_KB = SISAL_CAST(int32_t, v_ELSE_16101_n__0_KB));
            (v_LET_NON_REC_16102_n__0_N = SISAL_CAST(int32_t, v_ELSE_16101_n__0_N));
            (v_LET_NON_REC_16102_n__0_NEW_Y = SISAL_CAST(double, v_ELSE_16101_n__0_NEW_Y));
            (v_LET_NON_REC_16102_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_ELSE_16101_n__0_NEW_Z));
            (v_LET_NON_REC_16102_n__0_OLD_KB = SISAL_CAST(int32_t, v_ELSE_16101_n__0_OLD_KB));
            (v_LET_NON_REC_16102_n__0_OLD_NEW_Y = SISAL_CAST(double, v_ELSE_16101_n__0_OLD_NEW_Y));
            (v_LET_NON_REC_16102_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_ELSE_16101_n__0_OLD_NEW_Z));
            (v_LET_NON_REC_16102_n__0_YNORM = SISAL_CAST(double, v_ELSE_16101_n__0_YNORM));
            (v_LET_NON_REC_16102_n__0_Z = SISAL_CAST(sisal_array_t, v_ELSE_16101_n__0_Z));
            sisal_array_t v_IF_DOUBLE___16103_n__0_OLD_NEW_Z = {0};
            (v_IF_DOUBLE___16103_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_OLD_NEW_Z));
            int32_t v_IF_DOUBLE___16103_n__0_K = 0;
            (v_IF_DOUBLE___16103_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K));
            {
              int32_t v_PREDICATE_16104_n__0_K = 0;
              sisal_array_t v_PREDICATE_16104_n__0_OLD_NEW_Z = {0};
              (v_PREDICATE_16104_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___16103_n__0_OLD_NEW_Z));
              (v_PREDICATE_16104_n__0_K = SISAL_CAST(int32_t, v_IF_DOUBLE___16103_n__0_K));
              double v_PREDICATE_16104_n__1_p0_o = 0;
              (v_PREDICATE_16104_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_16104_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_PREDICATE_16104_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16104_n__0_OLD_NEW_Z).lower_bound[0])]));
              double v_PREDICATE_16104_n__2_p0_o = 0;
              (v_PREDICATE_16104_n__2_p0_o = SISAL_CAST(double, 0.));
              bool v_PREDICATE_16104_n__3_p0_o = 0;
              (v_PREDICATE_16104_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_16104_n__1_p0_o) == SISAL_CAST(double, v_PREDICATE_16104_n__2_p0_o))));
              if (v_PREDICATE_16104_n__3_p0_o) {
                double v_THEN_16106_n__1_p0_o = 0;
                (v_THEN_16106_n__1_p0_o = SISAL_CAST(double, 0));
              }
              else {
                double v_ELSE_16105_n__1_p0_o = 0;
                (v_ELSE_16105_n__1_p0_o = SISAL_CAST(double, 1.));
              }
            }
            sisal_array_t v_LET_NON_REC_16102_n__3_p0_o = {0};
            (v_LET_NON_REC_16102_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A), (SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A).lower_bound[0]))));
            float v_LET_NON_REC_16102_n__4_p0_o = 0;
            (v_LET_NON_REC_16102_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__3_p0_o).lower_bound[0])]));
            sisal_array_t v_LET_NON_REC_16102_n__5_p0_o = {0};
            (v_LET_NON_REC_16102_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A), (SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A).lower_bound[0]))));
            double v_LET_NON_REC_16102_n__6_p0_o = 0;
            (v_LET_NON_REC_16102_n__6_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__5_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__5_p0_o).lower_bound[0])]));
            float v_LET_NON_REC_16102_n__7_p0_o = 0;
            (v_LET_NON_REC_16102_n__7_p0_o = SISAL_CAST(float, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_16102_n__6_p0_o))));
            sisal_array_t v_LET_NON_REC_16102_n__8_p0_o = {0};
            (v_LET_NON_REC_16102_n__8_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A), (SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A).lower_bound[0]))));
            float v_LET_NON_REC_16102_n__9_p0_o = 0;
            (v_LET_NON_REC_16102_n__9_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__8_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__8_p0_o).lower_bound[0])]));
            sisal_array_t v_LET_NON_REC_16102_n__10_p0_o = {0};
            (v_LET_NON_REC_16102_n__10_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A), (SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_A).lower_bound[0]))));
            double v_LET_NON_REC_16102_n__11_p0_o = 0;
            (v_LET_NON_REC_16102_n__11_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__10_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__10_p0_o).lower_bound[0])]));
            double v_LET_NON_REC_16102_n__12_p0_o = 0;
            (v_LET_NON_REC_16102_n__12_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_16102_n__11_p0_o))));
            float v_LET_NON_REC_16102_n__13_p0_o = 0;
            (v_LET_NON_REC_16102_n__13_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_OLD_NEW_Z).lower_bound[0])]));
            double v_LET_NON_REC_16102_n__14_p0_o = 0;
            (v_LET_NON_REC_16102_n__14_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_OLD_NEW_Z).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_OLD_NEW_Z).lower_bound[0])]));
            double v_LET_NON_REC_16102_n__15_p0_o = 0;
            (v_LET_NON_REC_16102_n__15_p0_o = SISAL_CAST(double, func__SABS__D__D(SISAL_CAST(double, v_LET_NON_REC_16102_n__14_p0_o))));
            (v_LET_NON_REC_16102_n__16_S = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_16102_n__12_p0_o) / SISAL_CAST(double, v_LET_NON_REC_16102_n__15_p0_o))));
            int32_t v_LET_NON_REC_16102_n__17_p0_o = 0;
            (v_LET_NON_REC_16102_n__17_p0_o = SISAL_CAST(int32_t, 1));
            int32_t v_LET_NON_REC_16102_n__18_p0_o = 0;
            (v_LET_NON_REC_16102_n__18_p0_o = SISAL_CAST(int32_t, 1));
            sisal_array_t v_LET_NON_REC_16102_n__19_p0_o = {0};
            (v_LET_NON_REC_16102_n__19_p0_o = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__18_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_16102_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__0_OLD_NEW_Z), SISAL_CAST(double, v_LET_NON_REC_16102_n__16_S))));
            double v_LET_NON_REC_16102_n__20_p0_o = 0;
            (v_LET_NON_REC_16102_n__20_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_16102_n__0_OLD_NEW_Y) * SISAL_CAST(double, v_LET_NON_REC_16102_n__16_S))));
            (v_ELSE_16101_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16102_n__19_p0_o));
            (v_ELSE_16101_n__1_p1_o = SISAL_CAST(double, v_LET_NON_REC_16102_n__20_p0_o));
          }
          (v_BODY_16098_n__6_ZTEMP = SISAL_CAST(sisal_array_t, v_ELSE_16101_n__1_p0_o));
          (v_BODY_16098_n__6_NEW_Y = SISAL_CAST(double, v_ELSE_16101_n__1_p1_o));
        }
      }
      sisal_array_t v_IF_array_dv_DOUBLE____16108_n__0_A = {0};
      (v_IF_array_dv_DOUBLE____16108_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_A));
      int32_t v_IF_array_dv_DOUBLE____16108_n__0_K = 0;
      (v_IF_array_dv_DOUBLE____16108_n__0_K = SISAL_CAST(int32_t, v_BODY_16098_n__5_K));
      sisal_array_t v_IF_array_dv_DOUBLE____16108_n__0_ZTEMP = {0};
      (v_IF_array_dv_DOUBLE____16108_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_BODY_16098_n__6_ZTEMP));
      {
        sisal_array_t v_PREDICATE_16109_n__0_A = {0};
        int32_t v_PREDICATE_16109_n__0_K = 0;
        (v_PREDICATE_16109_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____16108_n__0_A));
        (v_PREDICATE_16109_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____16108_n__0_K));
        sisal_array_t v_PREDICATE_16109_n__1_p0_o = {0};
        (v_PREDICATE_16109_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_16109_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_16109_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16109_n__0_A).lower_bound[0]))));
        double v_PREDICATE_16109_n__2_p0_o = 0;
        (v_PREDICATE_16109_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_16109_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_16109_n__0_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_16109_n__1_p0_o).lower_bound[0])]));
        double v_PREDICATE_16109_n__3_p0_o = 0;
        (v_PREDICATE_16109_n__3_p0_o = SISAL_CAST(double, 0.));
        bool v_PREDICATE_16109_n__4_p0_o = 0;
        (v_PREDICATE_16109_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_16109_n__2_p0_o) == SISAL_CAST(double, v_PREDICATE_16109_n__3_p0_o))));
        if (v_PREDICATE_16109_n__4_p0_o) {
          int32_t v_THEN_16111_n__0_K = 0;
          sisal_array_t v_THEN_16111_n__0_ZTEMP = {0};
          (v_THEN_16111_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____16108_n__0_ZTEMP));
          (v_THEN_16111_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____16108_n__0_K));
          double v_THEN_16111_n__1_p0_o = 0;
          (v_THEN_16111_n__1_p0_o = SISAL_CAST(double, 1.));
          sisal_array_t v_THEN_16111_n__2_p0_o = {0};
          (v_THEN_16111_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_16111_n__0_ZTEMP), ((int64_t)SISAL_CAST(int32_t, v_THEN_16111_n__0_K)), SISAL_CAST(double, SISAL_CAST(double, v_THEN_16111_n__1_p0_o)))));
          (v_BODY_16098_n__8_ZTEMP2 = SISAL_CAST(sisal_array_t, v_THEN_16111_n__2_p0_o));
        }
        else {
          sisal_array_t v_ELSE_16110_n__0_A = {0};
          int32_t v_ELSE_16110_n__0_K = 0;
          sisal_array_t v_ELSE_16110_n__0_ZTEMP = {0};
          (v_ELSE_16110_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____16108_n__0_ZTEMP));
          (v_ELSE_16110_n__0_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____16108_n__0_K));
          (v_ELSE_16110_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____16108_n__0_A));
          float v_ELSE_16110_n__1_p0_o = 0;
          (v_ELSE_16110_n__1_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_ZTEMP).data)[(SISAL_CAST(int32_t, v_ELSE_16110_n__0_K) - SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_ZTEMP).lower_bound[0])]));
          double v_ELSE_16110_n__2_p0_o = 0;
          (v_ELSE_16110_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_ZTEMP).data)[(SISAL_CAST(int32_t, v_ELSE_16110_n__0_K) - SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_ZTEMP).lower_bound[0])]));
          sisal_array_t v_ELSE_16110_n__3_p0_o = {0};
          (v_ELSE_16110_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_A), (SISAL_CAST(int32_t, v_ELSE_16110_n__0_K) - SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_A).lower_bound[0]))));
          double v_ELSE_16110_n__4_p0_o = 0;
          (v_ELSE_16110_n__4_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_16110_n__3_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_16110_n__0_K) - SISAL_CAST(sisal_array_t, v_ELSE_16110_n__3_p0_o).lower_bound[0])]));
          double v_ELSE_16110_n__5_p0_o = 0;
          (v_ELSE_16110_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_16110_n__2_p0_o) / SISAL_CAST(double, v_ELSE_16110_n__4_p0_o))));
          sisal_array_t v_ELSE_16110_n__6_p0_o = {0};
          (v_ELSE_16110_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_ELSE_16110_n__0_ZTEMP), ((int64_t)SISAL_CAST(int32_t, v_ELSE_16110_n__0_K)), SISAL_CAST(double, SISAL_CAST(double, v_ELSE_16110_n__5_p0_o)))));
          (v_BODY_16098_n__8_ZTEMP2 = SISAL_CAST(sisal_array_t, v_ELSE_16110_n__6_p0_o));
        }
      }
      {
        sisal_array_t v_LET_NON_REC_16112_n__0_A = {0};
        int32_t v_LET_NON_REC_16112_n__0_K = 0;
        int32_t v_LET_NON_REC_16112_n__0_KB = 0;
        int32_t v_LET_NON_REC_16112_n__0_N = 0;
        double v_LET_NON_REC_16112_n__0_NEW_Y = 0;
        sisal_array_t v_LET_NON_REC_16112_n__0_NEW_Z = {0};
        int32_t v_LET_NON_REC_16112_n__0_OLD_KB = 0;
        double v_LET_NON_REC_16112_n__0_OLD_NEW_Y = 0;
        sisal_array_t v_LET_NON_REC_16112_n__0_OLD_NEW_Z = {0};
        double v_LET_NON_REC_16112_n__2_T = 0;
        double v_LET_NON_REC_16112_n__0_YNORM = 0;
        sisal_array_t v_LET_NON_REC_16112_n__0_Z = {0};
        sisal_array_t v_LET_NON_REC_16112_n__13_Z3 = {0};
        sisal_array_t v_LET_NON_REC_16112_n__15_Z4 = {0};
        sisal_array_t v_LET_NON_REC_16112_n__0_ZTEMP = {0};
        sisal_array_t v_LET_NON_REC_16112_n__0_ZTEMP2 = {0};
        (v_LET_NON_REC_16112_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_A));
        (v_LET_NON_REC_16112_n__0_K = SISAL_CAST(int32_t, v_BODY_16098_n__5_K));
        (v_LET_NON_REC_16112_n__0_KB = SISAL_CAST(int32_t, v_BODY_16098_n__2_KB));
        (v_LET_NON_REC_16112_n__0_N = SISAL_CAST(int32_t, v_BODY_16098_n__0_N));
        (v_LET_NON_REC_16112_n__0_NEW_Y = SISAL_CAST(double, v_BODY_16098_n__6_NEW_Y));
        (v_LET_NON_REC_16112_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_p4_o));
        (v_LET_NON_REC_16112_n__0_OLD_KB = SISAL_CAST(int32_t, v_BODY_16098_n__0_OLD_KB));
        (v_LET_NON_REC_16112_n__0_OLD_NEW_Y = SISAL_CAST(double, v_BODY_16098_n__0_OLD_NEW_Y));
        (v_LET_NON_REC_16112_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_OLD_NEW_Z));
        (v_LET_NON_REC_16112_n__0_YNORM = SISAL_CAST(double, v_BODY_16098_n__0_YNORM));
        (v_LET_NON_REC_16112_n__0_Z = SISAL_CAST(sisal_array_t, v_BODY_16098_n__0_Z));
        (v_LET_NON_REC_16112_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_BODY_16098_n__6_ZTEMP));
        (v_LET_NON_REC_16112_n__0_ZTEMP2 = SISAL_CAST(sisal_array_t, v_BODY_16098_n__8_ZTEMP2));
        double v_LET_NON_REC_16112_n__1_p0_o = 0;
        (v_LET_NON_REC_16112_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP2).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP2).lower_bound[0])]));
        (v_LET_NON_REC_16112_n__2_T = SISAL_CAST(double, (-SISAL_CAST(double, v_LET_NON_REC_16112_n__1_p0_o))));
        int32_t v_LET_NON_REC_16112_n__3_p0_o = 0;
        (v_LET_NON_REC_16112_n__3_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_LET_NON_REC_16112_n__4_p0_o = 0;
        (v_LET_NON_REC_16112_n__4_p0_o = SISAL_CAST(int32_t, 1));
        float v_LET_NON_REC_16112_n__5_p0_o = 0;
        (v_LET_NON_REC_16112_n__5_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_K) - SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__4_p0_o))));
        {
          sisal_array_t v_LET_NON_REC_16113_n__0_A = {0};
          int32_t v_LET_NON_REC_16113_n__0_K = 0;
          int32_t v_LET_NON_REC_16113_n__0_KB = 0;
          int32_t v_LET_NON_REC_16113_n__0_N = 0;
          double v_LET_NON_REC_16113_n__0_NEW_Y = 0;
          sisal_array_t v_LET_NON_REC_16113_n__0_NEW_Z = {0};
          int32_t v_LET_NON_REC_16113_n__0_OLD_KB = 0;
          double v_LET_NON_REC_16113_n__0_OLD_NEW_Y = 0;
          sisal_array_t v_LET_NON_REC_16113_n__0_OLD_NEW_Z = {0};
          double v_LET_NON_REC_16113_n__0_T = 0;
          sisal_array_t v_LET_NON_REC_16113_n__1_TRANS_A = {0};
          double v_LET_NON_REC_16113_n__0_YNORM = 0;
          sisal_array_t v_LET_NON_REC_16113_n__0_Z = {0};
          sisal_array_t v_LET_NON_REC_16113_n__0_ZTEMP = {0};
          sisal_array_t v_LET_NON_REC_16113_n__0_ZTEMP2 = {0};
          (v_LET_NON_REC_16113_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_A));
          (v_LET_NON_REC_16113_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_K));
          (v_LET_NON_REC_16113_n__0_KB = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_KB));
          (v_LET_NON_REC_16113_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_N));
          (v_LET_NON_REC_16113_n__0_NEW_Y = SISAL_CAST(double, v_LET_NON_REC_16112_n__0_NEW_Y));
          (v_LET_NON_REC_16113_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_NEW_Z));
          (v_LET_NON_REC_16113_n__0_OLD_KB = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_OLD_KB));
          (v_LET_NON_REC_16113_n__0_OLD_NEW_Y = SISAL_CAST(double, v_LET_NON_REC_16112_n__0_OLD_NEW_Y));
          (v_LET_NON_REC_16113_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_OLD_NEW_Z));
          (v_LET_NON_REC_16113_n__0_T = SISAL_CAST(double, v_LET_NON_REC_16112_n__2_T));
          (v_LET_NON_REC_16113_n__0_YNORM = SISAL_CAST(double, v_LET_NON_REC_16112_n__0_YNORM));
          (v_LET_NON_REC_16113_n__0_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_Z));
          (v_LET_NON_REC_16113_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP));
          (v_LET_NON_REC_16113_n__0_ZTEMP2 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP2));
          (v_LET_NON_REC_16113_n__1_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16113_n__0_A))));
          sisal_array_t v_LET_NON_REC_16113_n__2_p0_o = {0};
          (v_LET_NON_REC_16113_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16113_n__1_TRANS_A), (SISAL_CAST(int32_t, v_LET_NON_REC_16113_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16113_n__1_TRANS_A).lower_bound[0]))));
        }
        int32_t v_LET_NON_REC_16112_n__8_p0_o = 0;
        (v_LET_NON_REC_16112_n__8_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_LET_NON_REC_16112_n__9_p0_o = 0;
        (v_LET_NON_REC_16112_n__9_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_LET_NON_REC_16112_n__10_p0_o = 0;
        (v_LET_NON_REC_16112_n__10_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_K) - SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__9_p0_o))));
        sisal_array_t v_LET_NON_REC_16112_n__11_p0_o = {0};
        {
          sisal_array_t v_LET_NON_REC_16114_n__0_A = {0};
          int32_t v_LET_NON_REC_16114_n__0_K = 0;
          int32_t v_LET_NON_REC_16114_n__0_KB = 0;
          int32_t v_LET_NON_REC_16114_n__0_N = 0;
          double v_LET_NON_REC_16114_n__0_NEW_Y = 0;
          sisal_array_t v_LET_NON_REC_16114_n__0_NEW_Z = {0};
          int32_t v_LET_NON_REC_16114_n__0_OLD_KB = 0;
          double v_LET_NON_REC_16114_n__0_OLD_NEW_Y = 0;
          sisal_array_t v_LET_NON_REC_16114_n__0_OLD_NEW_Z = {0};
          double v_LET_NON_REC_16114_n__0_T = 0;
          sisal_array_t v_LET_NON_REC_16114_n__1_TRANS_A = {0};
          double v_LET_NON_REC_16114_n__0_YNORM = 0;
          sisal_array_t v_LET_NON_REC_16114_n__0_Z = {0};
          sisal_array_t v_LET_NON_REC_16114_n__0_ZTEMP = {0};
          sisal_array_t v_LET_NON_REC_16114_n__0_ZTEMP2 = {0};
          (v_LET_NON_REC_16114_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_A));
          (v_LET_NON_REC_16114_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_K));
          (v_LET_NON_REC_16114_n__0_KB = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_KB));
          (v_LET_NON_REC_16114_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_N));
          (v_LET_NON_REC_16114_n__0_NEW_Y = SISAL_CAST(double, v_LET_NON_REC_16112_n__0_NEW_Y));
          (v_LET_NON_REC_16114_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_NEW_Z));
          (v_LET_NON_REC_16114_n__0_OLD_KB = SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__0_OLD_KB));
          (v_LET_NON_REC_16114_n__0_OLD_NEW_Y = SISAL_CAST(double, v_LET_NON_REC_16112_n__0_OLD_NEW_Y));
          (v_LET_NON_REC_16114_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_OLD_NEW_Z));
          (v_LET_NON_REC_16114_n__0_T = SISAL_CAST(double, v_LET_NON_REC_16112_n__2_T));
          (v_LET_NON_REC_16114_n__0_YNORM = SISAL_CAST(double, v_LET_NON_REC_16112_n__0_YNORM));
          (v_LET_NON_REC_16114_n__0_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_Z));
          (v_LET_NON_REC_16114_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP));
          (v_LET_NON_REC_16114_n__0_ZTEMP2 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP2));
          (v_LET_NON_REC_16114_n__1_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16114_n__0_A))));
          sisal_array_t v_LET_NON_REC_16114_n__2_p0_o = {0};
          (v_LET_NON_REC_16114_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16114_n__1_TRANS_A), (SISAL_CAST(int32_t, v_LET_NON_REC_16114_n__0_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_16114_n__1_TRANS_A).lower_bound[0]))));
          (v_LET_NON_REC_16112_n__11_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16114_n__2_p0_o));
        }
        (v_LET_NON_REC_16112_n__13_Z3 = SISAL_CAST(sisal_array_t, func_SAXPY(SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__8_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_16112_n__10_p0_o), SISAL_CAST(double, v_LET_NON_REC_16112_n__2_T), SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__11_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__0_ZTEMP2))));
        sisal_array_t v_LET_NON_REC_16112_n__14_p0_o = {0};
        {
          sisal_array_t v_FORALL_16115_n__0_A = v_LET_NON_REC_16112_n__0_A;
          int32_t v_FORALL_16115_n__2_I;
          int32_t v_FORALL_16115_n__0_K = v_LET_NON_REC_16112_n__0_K;
          int32_t v_FORALL_16115_n__0_KB = v_LET_NON_REC_16112_n__0_KB;
          int32_t v_FORALL_16115_n__0_N = v_LET_NON_REC_16112_n__0_N;
          double v_FORALL_16115_n__0_NEW_Y = v_LET_NON_REC_16112_n__0_NEW_Y;
          sisal_array_t v_FORALL_16115_n__0_NEW_Z = v_LET_NON_REC_16112_n__0_NEW_Z;
          int32_t v_FORALL_16115_n__0_OLD_KB = v_LET_NON_REC_16112_n__0_OLD_KB;
          double v_FORALL_16115_n__0_OLD_NEW_Y = v_LET_NON_REC_16112_n__0_OLD_NEW_Y;
          sisal_array_t v_FORALL_16115_n__0_OLD_NEW_Z = v_LET_NON_REC_16112_n__0_OLD_NEW_Z;
          double v_FORALL_16115_n__0_T = v_LET_NON_REC_16112_n__2_T;
          double v_FORALL_16115_n__0_YNORM = v_LET_NON_REC_16112_n__0_YNORM;
          sisal_array_t v_FORALL_16115_n__0_Z = v_LET_NON_REC_16112_n__0_Z;
          sisal_array_t v_FORALL_16115_n__0_Z3 = v_LET_NON_REC_16112_n__13_Z3;
          sisal_array_t v_FORALL_16115_n__0_ZTEMP = v_LET_NON_REC_16112_n__0_ZTEMP;
          sisal_array_t v_FORALL_16115_n__0_ZTEMP2 = v_LET_NON_REC_16112_n__0_ZTEMP2;
          double v_FORALL_16115_n__3___forall_body_0;
          int32_t v_FORALL_16115_n__2___forall_lb_1_0;
          int32_t v_FORALL_16115_n__2___forall_ub_1_0;
          sisal_array_t v_GENERATOR_16117_n__0_A;
          int32_t v_GENERATOR_16117_n__1_I;
          int32_t v_GENERATOR_16117_n__0_K;
          int32_t v_GENERATOR_16117_n__0_KB;
          int32_t v_GENERATOR_16117_n__0_N;
          double v_GENERATOR_16117_n__0_NEW_Y;
          sisal_array_t v_GENERATOR_16117_n__0_NEW_Z;
          int32_t v_GENERATOR_16117_n__0_OLD_KB;
          double v_GENERATOR_16117_n__0_OLD_NEW_Y;
          sisal_array_t v_GENERATOR_16117_n__0_OLD_NEW_Z;
          double v_GENERATOR_16117_n__0_T;
          double v_GENERATOR_16117_n__0_YNORM;
          sisal_array_t v_GENERATOR_16117_n__0_Z;
          sisal_array_t v_GENERATOR_16117_n__0_Z3;
          sisal_array_t v_GENERATOR_16117_n__0_ZTEMP;
          sisal_array_t v_GENERATOR_16117_n__0_ZTEMP2;
          int32_t v_GENERATOR_16117_n__1___forall_lb_1_0;
          int32_t v_GENERATOR_16117_n__1___forall_ub_1_0;
          sisal_array_t v_BODY_16118_n__0_A;
          int32_t v_BODY_16118_n__0_I;
          int32_t v_BODY_16118_n__0_K;
          int32_t v_BODY_16118_n__0_KB;
          int32_t v_BODY_16118_n__0_N;
          double v_BODY_16118_n__0_NEW_Y;
          sisal_array_t v_BODY_16118_n__0_NEW_Z;
          int32_t v_BODY_16118_n__0_OLD_KB;
          double v_BODY_16118_n__0_OLD_NEW_Y;
          sisal_array_t v_BODY_16118_n__0_OLD_NEW_Z;
          double v_BODY_16118_n__0_T;
          double v_BODY_16118_n__0_YNORM;
          sisal_array_t v_BODY_16118_n__0_Z;
          sisal_array_t v_BODY_16118_n__0_Z3;
          sisal_array_t v_BODY_16118_n__0_ZTEMP;
          sisal_array_t v_BODY_16118_n__0_ZTEMP2;
          int32_t v_BODY_16118_n__0___forall_lb_1_0;
          int32_t v_BODY_16118_n__0___forall_ub_1_0;
          (v_GENERATOR_16117_n__0_K = v_FORALL_16115_n__0_K);
          (v_GENERATOR_16117_n__0_N = v_FORALL_16115_n__0_N);
          (v_LET_NON_REC_16112_n__14_p0_o = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_16117_n__0_N - v_GENERATOR_16117_n__0_K) + 1)))));
          (v_LET_NON_REC_16112_n__14_p0_o.dims[0] = ((v_GENERATOR_16117_n__0_N - v_GENERATOR_16117_n__0_K) + 1));
          (v_LET_NON_REC_16112_n__14_p0_o.lower_bound[0] = v_GENERATOR_16117_n__0_K);
          int32_t __g_16115 = 0;
          (v_GENERATOR_16117_n__1___forall_lb_1_0 = v_GENERATOR_16117_n__0_K);
          (v_GENERATOR_16117_n__1___forall_ub_1_0 = v_GENERATOR_16117_n__0_N);
          for ((v_GENERATOR_16117_n__1_I = v_GENERATOR_16117_n__0_K); (v_GENERATOR_16117_n__1_I <= v_GENERATOR_16117_n__0_N); (v_GENERATOR_16117_n__1_I++)) {
            (v_BODY_16118_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_A));
            (v_BODY_16118_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_16117_n__1_I));
            (v_BODY_16118_n__0_K = SISAL_CAST(int32_t, v_FORALL_16115_n__0_K));
            (v_BODY_16118_n__0_KB = SISAL_CAST(int32_t, v_FORALL_16115_n__0_KB));
            (v_BODY_16118_n__0_N = SISAL_CAST(int32_t, v_FORALL_16115_n__0_N));
            (v_BODY_16118_n__0_NEW_Y = SISAL_CAST(double, v_FORALL_16115_n__0_NEW_Y));
            (v_BODY_16118_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_NEW_Z));
            (v_BODY_16118_n__0_OLD_KB = SISAL_CAST(int32_t, v_FORALL_16115_n__0_OLD_KB));
            (v_BODY_16118_n__0_OLD_NEW_Y = SISAL_CAST(double, v_FORALL_16115_n__0_OLD_NEW_Y));
            (v_BODY_16118_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_OLD_NEW_Z));
            (v_BODY_16118_n__0_T = SISAL_CAST(double, v_FORALL_16115_n__0_T));
            (v_BODY_16118_n__0_YNORM = SISAL_CAST(double, v_FORALL_16115_n__0_YNORM));
            (v_BODY_16118_n__0_Z = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_Z));
            (v_BODY_16118_n__0_Z3 = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_Z3));
            (v_BODY_16118_n__0_ZTEMP = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_ZTEMP));
            (v_BODY_16118_n__0_ZTEMP2 = SISAL_CAST(sisal_array_t, v_FORALL_16115_n__0_ZTEMP2));
            (v_BODY_16118_n__0___forall_lb_1_0 = SISAL_CAST(int32_t, v_GENERATOR_16117_n__1___forall_lb_1_0));
            (v_BODY_16118_n__0___forall_ub_1_0 = SISAL_CAST(int32_t, v_GENERATOR_16117_n__1___forall_ub_1_0));
            double v_BODY_16118_n__1_p0_o = 0;
            (v_BODY_16118_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_16118_n__0_ZTEMP2).data)[(SISAL_CAST(int32_t, v_BODY_16118_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_16118_n__0_ZTEMP2).lower_bound[0])]));
            (((double *)v_LET_NON_REC_16112_n__14_p0_o.data)[__g_16115] = SISAL_CAST(double, v_BODY_16118_n__1_p0_o));
            (__g_16115++);
          }
        }
        sisal_array_t v_LET_NON_REC_16112_n__16_p0_o = {0};
        (v_LET_NON_REC_16112_n__16_p0_o = SISAL_CAST(sisal_array_t, sisal_array_addh_arr(SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__13_Z3), SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__14_p0_o))));
        (v_BODY_16098_n__10_NEW_Z = SISAL_CAST(sisal_array_t, v_LET_NON_REC_16112_n__16_p0_o));
      }
      bool v_BODY_16098_n__12_p0_o = 0;
      (v_BODY_16098_n__12_p0_o = SISAL_CAST(bool, false));
      (v_LoopB_16097_bodycap_n2_p0 = v_BODY_16098_n__2_KB);
      (v_LoopB_16097_bodycap_n6_p1 = v_BODY_16098_n__6_NEW_Y);
      (v_LoopB_16097_bodycap_n10_p0 = v_BODY_16098_n__10_NEW_Z);
      (v_LoopB_16097_bodycap_n12_p0 = v_BODY_16098_n__12_p0_o);
      (v_LoopB_16097_n__5_MERGE_KB = v_LoopB_16097_bodycap_n2_p0);
      (v_LoopB_16097_n__6_MERGE_NEW_Y = v_LoopB_16097_bodycap_n6_p1);
      (v_LoopB_16097_n__7_MERGE_NEW_Z = v_LoopB_16097_bodycap_n10_p0);
      (v_LoopB_16097_n__8_MERGE_OLD_KB = v_LoopB_16097_bodycap_n2_p0);
      (v_LoopB_16097_n__9_MERGE_OLD_NEW_Y = v_LoopB_16097_bodycap_n6_p1);
      (v_LoopB_16097_n__10_MERGE_OLD_NEW_Z = v_LoopB_16097_bodycap_n10_p0);
      (v_LoopB_16097_n__11_MERGE_first = v_LoopB_16097_bodycap_n12_p0);
      (v_TEST_16120_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_A));
      (v_TEST_16120_n__0_KB = SISAL_CAST(int32_t, v_LoopB_16097_n__5_MERGE_KB));
      (v_TEST_16120_n__0_N = SISAL_CAST(int32_t, v_LoopB_16097_n__0_N));
      (v_TEST_16120_n__0_NEW_Y = SISAL_CAST(double, v_LoopB_16097_n__6_MERGE_NEW_Y));
      (v_TEST_16120_n__0_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__7_MERGE_NEW_Z));
      (v_TEST_16120_n__0_OLD_KB = SISAL_CAST(int32_t, v_LoopB_16097_n__8_MERGE_OLD_KB));
      (v_TEST_16120_n__0_OLD_NEW_Y = SISAL_CAST(double, v_LoopB_16097_n__9_MERGE_OLD_NEW_Y));
      (v_TEST_16120_n__0_OLD_NEW_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__10_MERGE_OLD_NEW_Z));
      (v_TEST_16120_n__0_YNORM = SISAL_CAST(double, v_LoopB_16097_n__0_YNORM));
      (v_TEST_16120_n__0_Z = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__0_Z));
      (v_TEST_16120_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_16120_n__0_KB) <= SISAL_CAST(int32_t, v_TEST_16120_n__0_N))));
    }
    sisal_array_t v_RETURNS_16119_n__0_p0_o = {0};
    double v_RETURNS_16119_n__0_p1_o = 0;
    (v_RETURNS_16119_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_16097_n__10_MERGE_OLD_NEW_Z));
    (v_RETURNS_16119_n__0_p1_o = SISAL_CAST(double, v_LoopB_16097_n__9_MERGE_OLD_NEW_Y));
    sisal_array_t v_RETURNS_16119_n__1_p0_o = {0};
    (v_RETURNS_16119_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_16119_n__0_p0_o)));
    double v_RETURNS_16119_n__2_p0_o = 0;
    (v_RETURNS_16119_n__2_p0_o = SISAL_CAST(double, SISAL_CAST(double, v_RETURNS_16119_n__0_p1_o)));
    (v_g10_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_16119_n__1_p0_o));
    (v_g10_n__1_p1_o = SISAL_CAST(double, v_RETURNS_16119_n__2_p0_o));
  }
  (v_g10_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g10_n__1_p0_o));
  (v_g10_n__0_p1_i = SISAL_CAST(double, v_g10_n__1_p1_o));
  struct FUNC_CALC_NEWZY2_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g10_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(double, v_g10_n__0_p1_i));
  return __res_obj;
}

extern "C" double func_SASUM(int32_t N, sisal_array_t SX) {
  int32_t v_g11_n__0_N = 0;
  sisal_array_t v_g11_n__0_SX = {0};
  (v_g11_n__0_N = SISAL_CAST(int32_t, N));
  (v_g11_n__0_SX = SISAL_CAST(sisal_array_t, SX));
  double v_g11_n__0_p0_i = 0;
  double v_g11_n__1_p0_o = 0;
  {
    int32_t v_FORALL_15089_n__2_I;
    int32_t v_FORALL_15089_n__0_N = v_g11_n__0_N;
    sisal_array_t v_FORALL_15089_n__0_SX = v_g11_n__0_SX;
    double v_FORALL_15089_n__3___forall_body_0;
    int32_t v_FORALL_15089_n__2___forall_lb_2_0;
    int32_t v_FORALL_15089_n__2___forall_ub_2_0;
    int32_t v_GENERATOR_15091_n__2_I;
    int32_t v_GENERATOR_15091_n__0_N;
    sisal_array_t v_GENERATOR_15091_n__0_SX;
    int32_t v_GENERATOR_15091_n__2___forall_lb_2_0;
    int32_t v_GENERATOR_15091_n__2___forall_ub_2_0;
    int32_t v_BODY_15092_n__0_I;
    int32_t v_BODY_15092_n__0_N;
    sisal_array_t v_BODY_15092_n__0_SX;
    int32_t v_BODY_15092_n__0___forall_lb_2_0;
    int32_t v_BODY_15092_n__0___forall_ub_2_0;
    int32_t v_IF_DOUBLE___15093_n__0_I;
    sisal_array_t v_IF_DOUBLE___15093_n__0_SX;
    int32_t v_PREDICATE_15094_n__0_I;
    sisal_array_t v_PREDICATE_15094_n__0_SX;
    int32_t v_ELSE_15095_n__0_I;
    sisal_array_t v_ELSE_15095_n__0_SX;
    int32_t v_THEN_15096_n__0_I;
    sisal_array_t v_THEN_15096_n__0_SX;
    (v_GENERATOR_15091_n__0_N = v_FORALL_15089_n__0_N);
    (v_g11_n__1_p0_o = 0);
    (v_GENERATOR_15091_n__2___forall_lb_2_0 = 1);
    (v_GENERATOR_15091_n__2___forall_ub_2_0 = v_GENERATOR_15091_n__0_N);
    for ((v_GENERATOR_15091_n__2_I = 1); (v_GENERATOR_15091_n__2_I <= v_GENERATOR_15091_n__0_N); (v_GENERATOR_15091_n__2_I++)) {
      (v_BODY_15092_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_15091_n__2_I));
      (v_BODY_15092_n__0_N = SISAL_CAST(int32_t, v_FORALL_15089_n__0_N));
      (v_BODY_15092_n__0_SX = SISAL_CAST(sisal_array_t, v_FORALL_15089_n__0_SX));
      (v_BODY_15092_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_15091_n__2___forall_lb_2_0));
      (v_BODY_15092_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_15091_n__2___forall_ub_2_0));
      double v_BODY_15092_n__1_p0_o = 0;
      (v_IF_DOUBLE___15093_n__0_SX = SISAL_CAST(sisal_array_t, v_BODY_15092_n__0_SX));
      (v_IF_DOUBLE___15093_n__0_I = SISAL_CAST(int32_t, v_BODY_15092_n__0_I));
      {
        (v_PREDICATE_15094_n__0_SX = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___15093_n__0_SX));
        (v_PREDICATE_15094_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE___15093_n__0_I));
        double v_PREDICATE_15094_n__1_p0_o = 0;
        (v_PREDICATE_15094_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_15094_n__0_SX).data)[(SISAL_CAST(int32_t, v_PREDICATE_15094_n__0_I) - SISAL_CAST(sisal_array_t, v_PREDICATE_15094_n__0_SX).lower_bound[0])]));
        double v_PREDICATE_15094_n__2_p0_o = 0;
        (v_PREDICATE_15094_n__2_p0_o = SISAL_CAST(double, 0.));
        bool v_PREDICATE_15094_n__3_p0_o = 0;
        (v_PREDICATE_15094_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_15094_n__1_p0_o) < SISAL_CAST(double, v_PREDICATE_15094_n__2_p0_o))));
        if (v_PREDICATE_15094_n__3_p0_o) {
          (v_THEN_15096_n__0_SX = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___15093_n__0_SX));
          (v_THEN_15096_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE___15093_n__0_I));
          double v_THEN_15096_n__1_p0_o = 0;
          (v_THEN_15096_n__1_p0_o = SISAL_CAST(double, 1.));
          double v_THEN_15096_n__2_p0_o = 0;
          (v_THEN_15096_n__2_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_THEN_15096_n__1_p0_o))));
          double v_THEN_15096_n__3_p0_o = 0;
          (v_THEN_15096_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_15096_n__0_SX).data)[(SISAL_CAST(int32_t, v_THEN_15096_n__0_I) - SISAL_CAST(sisal_array_t, v_THEN_15096_n__0_SX).lower_bound[0])]));
          double v_THEN_15096_n__4_p0_o = 0;
          (v_THEN_15096_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_THEN_15096_n__2_p0_o) * SISAL_CAST(double, v_THEN_15096_n__3_p0_o))));
          (v_BODY_15092_n__1_p0_o = SISAL_CAST(double, v_THEN_15096_n__4_p0_o));
        }
        else {
          (v_ELSE_15095_n__0_SX = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___15093_n__0_SX));
          (v_ELSE_15095_n__0_I = SISAL_CAST(int32_t, v_IF_DOUBLE___15093_n__0_I));
          double v_ELSE_15095_n__1_p0_o = 0;
          (v_ELSE_15095_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_15095_n__0_SX).data)[(SISAL_CAST(int32_t, v_ELSE_15095_n__0_I) - SISAL_CAST(sisal_array_t, v_ELSE_15095_n__0_SX).lower_bound[0])]));
          (v_BODY_15092_n__1_p0_o = SISAL_CAST(double, v_ELSE_15095_n__1_p0_o));
        }
      }
      (v_g11_n__1_p0_o = (v_g11_n__1_p0_o + SISAL_CAST(double, v_BODY_15092_n__1_p0_o)));
    }
  }
  (v_g11_n__0_p0_i = SISAL_CAST(double, v_g11_n__1_p0_o));
  return SISAL_CAST(double, v_g11_n__0_p0_i);
}

extern "C" struct FUNC_SGEFA_results func_SGEFA(sisal_array_t A, int32_t LDA, int32_t N) {
  sisal_array_t v_g12_n__0_A = {0};
  int32_t v_g12_n__0_LDA = 0;
  int32_t v_g12_n__0_N = 0;
  (v_g12_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g12_n__0_LDA = SISAL_CAST(int32_t, LDA));
  (v_g12_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g12_n__0_p0_i = {0};
  sisal_array_t v_g12_n__0_p1_i = {0};
  int32_t v_g12_n__0_p2_i = 0;
  sisal_array_t v_g12_n__1_p0_o = {0};
  sisal_array_t v_g12_n__1_p1_o = {0};
  int32_t v_g12_n__1_p2_o = 0;
  {
    sisal_array_t v_LET_NON_REC_14056_n__0_A = {0};
    int32_t v_LET_NON_REC_14056_n__0_LDA = 0;
    int32_t v_LET_NON_REC_14056_n__2_LINFO = 0;
    sisal_array_t v_LET_NON_REC_14056_n__2_LIPVT = {0};
    sisal_array_t v_LET_NON_REC_14056_n__2_LLU = {0};
    int32_t v_LET_NON_REC_14056_n__0_N = 0;
    (v_LET_NON_REC_14056_n__0_A = SISAL_CAST(sisal_array_t, v_g12_n__0_A));
    (v_LET_NON_REC_14056_n__0_LDA = SISAL_CAST(int32_t, v_g12_n__0_LDA));
    (v_LET_NON_REC_14056_n__0_N = SISAL_CAST(int32_t, v_g12_n__0_N));
    int32_t v_LET_NON_REC_14056_n__1_p0_o = 0;
    sisal_array_t v_LET_NON_REC_14056_n__1_p1_o = {0};
    sisal_array_t v_LET_NON_REC_14056_n__1_p2_o = {0};
    {
      int32_t v_LoopB_14057_n__5_MERGE_INFO = 0;
      sisal_array_t v_LoopB_14057_n__6_MERGE_IPVT = {0};
      int32_t v_LoopB_14057_n__7_MERGE_K = 0;
      sisal_array_t v_LoopB_14057_n__8_MERGE_LU = {0};
      int32_t v_LoopB_14057_n__9_MERGE_OLD_INFO = 0;
      sisal_array_t v_LoopB_14057_n__10_MERGE_OLD_IPVT = {0};
      int32_t v_LoopB_14057_n__11_MERGE_OLD_K = 0;
      sisal_array_t v_LoopB_14057_n__12_MERGE_OLD_LU = {0};
      bool v_LoopB_14057_n__13_MERGE_first = 0;
      int32_t v_LoopB_14057_bodycap_n2_p0 = 0;
      sisal_array_t v_LoopB_14057_bodycap_n17_p0 = {0};
      int32_t v_LoopB_14057_bodycap_n18_p0 = 0;
      sisal_array_t v_LoopB_14057_bodycap_n18_p1 = {0};
      bool v_LoopB_14057_bodycap_n20_p0 = 0;
      sisal_array_t v_LoopB_14057_n__0_A = {0};
      (v_LoopB_14057_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14056_n__0_A));
      int32_t v_LoopB_14057_n__0_LDA = 0;
      (v_LoopB_14057_n__0_LDA = SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__0_LDA));
      int32_t v_LoopB_14057_n__0_N = 0;
      (v_LoopB_14057_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__0_N));
      sisal_array_t v_INIT_14084_n__0_A = {0};
      int32_t v_INIT_14084_n__2_INFO = 0;
      sisal_array_t v_INIT_14084_n__3_IPVT = {0};
      int32_t v_INIT_14084_n__1_K = 0;
      int32_t v_INIT_14084_n__0_LDA = 0;
      sisal_array_t v_INIT_14084_n__0_LU = {0};
      int32_t v_INIT_14084_n__0_N = 0;
      int32_t v_INIT_14084_n__2_OLD_INFO = 0;
      sisal_array_t v_INIT_14084_n__3_OLD_IPVT = {0};
      int32_t v_INIT_14084_n__1_OLD_K = 0;
      sisal_array_t v_INIT_14084_n__0_OLD_LU = {0};
      (v_INIT_14084_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__0_A));
      (v_INIT_14084_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14057_n__0_LDA));
      (v_INIT_14084_n__0_N = SISAL_CAST(int32_t, v_LoopB_14057_n__0_N));
      (v_INIT_14084_n__1_OLD_K = SISAL_CAST(int32_t, 1));
      (v_INIT_14084_n__2_OLD_INFO = SISAL_CAST(int32_t, 0));
      int32_t v_INIT_14084_n__4_p0_o = 0;
      (v_INIT_14084_n__4_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_INIT_14084_n__5_p0_o = 0;
      (v_INIT_14084_n__5_p0_o = SISAL_CAST(int32_t, 0));
      (v_INIT_14084_n__3_OLD_IPVT = SISAL_CAST(sisal_array_t, sisal_array_fill_i32(((int64_t)SISAL_CAST(int32_t, v_INIT_14084_n__4_p0_o)), ((int64_t)SISAL_CAST(int32_t, v_INIT_14084_n__0_N)), SISAL_CAST(int32_t, v_INIT_14084_n__5_p0_o))));
      bool v_INIT_14084_n__6_p0_o = 0;
      (v_INIT_14084_n__6_p0_o = SISAL_CAST(bool, true));
      (v_LoopB_14057_n__5_MERGE_INFO = v_INIT_14084_n__2_OLD_INFO);
      (v_LoopB_14057_n__6_MERGE_IPVT = v_INIT_14084_n__3_OLD_IPVT);
      (v_LoopB_14057_n__7_MERGE_K = v_INIT_14084_n__1_OLD_K);
      (v_LoopB_14057_n__8_MERGE_LU = v_INIT_14084_n__0_OLD_LU);
      (v_LoopB_14057_n__9_MERGE_OLD_INFO = v_INIT_14084_n__2_OLD_INFO);
      (v_LoopB_14057_n__10_MERGE_OLD_IPVT = v_INIT_14084_n__3_OLD_IPVT);
      (v_LoopB_14057_n__11_MERGE_OLD_K = v_INIT_14084_n__1_OLD_K);
      (v_LoopB_14057_n__12_MERGE_OLD_LU = v_INIT_14084_n__0_OLD_LU);
      (v_LoopB_14057_n__13_MERGE_first = v_INIT_14084_n__6_p0_o);
      sisal_array_t v_TEST_14083_n__0_A = {0};
      int32_t v_TEST_14083_n__0_INFO = 0;
      sisal_array_t v_TEST_14083_n__0_IPVT = {0};
      int32_t v_TEST_14083_n__0_K = 0;
      int32_t v_TEST_14083_n__0_LDA = 0;
      sisal_array_t v_TEST_14083_n__0_LU = {0};
      int32_t v_TEST_14083_n__0_N = 0;
      int32_t v_TEST_14083_n__0_OLD_INFO = 0;
      sisal_array_t v_TEST_14083_n__0_OLD_IPVT = {0};
      int32_t v_TEST_14083_n__0_OLD_K = 0;
      sisal_array_t v_TEST_14083_n__0_OLD_LU = {0};
      (v_TEST_14083_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__0_A));
      (v_TEST_14083_n__0_INFO = SISAL_CAST(int32_t, v_LoopB_14057_n__5_MERGE_INFO));
      (v_TEST_14083_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__6_MERGE_IPVT));
      (v_TEST_14083_n__0_K = SISAL_CAST(int32_t, v_LoopB_14057_n__7_MERGE_K));
      (v_TEST_14083_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14057_n__0_LDA));
      (v_TEST_14083_n__0_LU = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__8_MERGE_LU));
      (v_TEST_14083_n__0_N = SISAL_CAST(int32_t, v_LoopB_14057_n__0_N));
      (v_TEST_14083_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14057_n__9_MERGE_OLD_INFO));
      (v_TEST_14083_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__10_MERGE_OLD_IPVT));
      (v_TEST_14083_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14057_n__11_MERGE_OLD_K));
      (v_TEST_14083_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__12_MERGE_OLD_LU));
      int32_t v_TEST_14083_n__1_p0_o = 0;
      (v_TEST_14083_n__1_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_TEST_14083_n__2_p0_o = 0;
      (v_TEST_14083_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_TEST_14083_n__0_N) - SISAL_CAST(int32_t, v_TEST_14083_n__1_p0_o))));
      bool v_TEST_14083_n__3_p0_o = 0;
      (v_TEST_14083_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_14083_n__0_K) <= SISAL_CAST(int32_t, v_TEST_14083_n__2_p0_o))));
      #ifdef SISAL_TRAP_ZERO_TRIP
      if ((!v_TEST_14083_n__3_p0_o)) {
        fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_14057 executed 0 times (guard false on entry)\n");
        exit(1);
      }
      #endif
      while (v_TEST_14083_n__3_p0_o) {
        sisal_array_t v_BODY_14058_n__0_A = {0};
        int32_t v_BODY_14058_n__18_INFO = 0;
        sisal_array_t v_BODY_14058_n__17_IPVT = {0};
        int32_t v_BODY_14058_n__2_K = 0;
        int32_t v_BODY_14058_n__16_L = 0;
        int32_t v_BODY_14058_n__0_LDA = 0;
        sisal_array_t v_BODY_14058_n__18_LU = {0};
        int32_t v_BODY_14058_n__0_N = 0;
        int32_t v_BODY_14058_n__0_OLD_INFO = 0;
        sisal_array_t v_BODY_14058_n__0_OLD_IPVT = {0};
        int32_t v_BODY_14058_n__0_OLD_K = 0;
        sisal_array_t v_BODY_14058_n__0_OLD_LU = {0};
        int32_t v_BODY_14058_n__0_p1_o = 0;
        sisal_array_t v_BODY_14058_n__0_p2_o = {0};
        sisal_array_t v_BODY_14058_n__0_p5_o = {0};
        (v_BODY_14058_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__0_A));
        (v_BODY_14058_n__0_p1_o = SISAL_CAST(int32_t, v_LoopB_14057_n__5_MERGE_INFO));
        (v_BODY_14058_n__0_p2_o = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__6_MERGE_IPVT));
        int32_t v_BODY_14058_n__0_p3_o = 0;
        (v_BODY_14058_n__0_p3_o = SISAL_CAST(int32_t, v_LoopB_14057_n__7_MERGE_K));
        (v_BODY_14058_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14057_n__0_LDA));
        (v_BODY_14058_n__0_p5_o = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__8_MERGE_LU));
        (v_BODY_14058_n__0_N = SISAL_CAST(int32_t, v_LoopB_14057_n__0_N));
        (v_BODY_14058_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14057_n__9_MERGE_OLD_INFO));
        (v_BODY_14058_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__10_MERGE_OLD_IPVT));
        (v_BODY_14058_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14057_n__11_MERGE_OLD_K));
        (v_BODY_14058_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__12_MERGE_OLD_LU));
        int32_t v_BODY_14058_n__1_p0_o = 0;
        (v_BODY_14058_n__1_p0_o = SISAL_CAST(int32_t, 1));
        (v_BODY_14058_n__2_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K) + SISAL_CAST(int32_t, v_BODY_14058_n__1_p0_o))));
        int32_t v_BODY_14058_n__3_p0_o = 0;
        (v_BODY_14058_n__3_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14058_n__0_N) - SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K))));
        int32_t v_BODY_14058_n__4_p0_o = 0;
        (v_BODY_14058_n__4_p0_o = SISAL_CAST(int32_t, 1));
        float v_BODY_14058_n__5_p0_o = 0;
        (v_BODY_14058_n__5_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_BODY_14058_n__3_p0_o) + SISAL_CAST(int32_t, v_BODY_14058_n__4_p0_o))));
        {
          sisal_array_t v_LET_NON_REC_14059_n__0_A = {0};
          int32_t v_LET_NON_REC_14059_n__0_INFO = 0;
          sisal_array_t v_LET_NON_REC_14059_n__0_IPVT = {0};
          int32_t v_LET_NON_REC_14059_n__0_K = 0;
          int32_t v_LET_NON_REC_14059_n__0_LDA = 0;
          sisal_array_t v_LET_NON_REC_14059_n__0_LU = {0};
          int32_t v_LET_NON_REC_14059_n__0_N = 0;
          int32_t v_LET_NON_REC_14059_n__0_OLD_INFO = 0;
          sisal_array_t v_LET_NON_REC_14059_n__0_OLD_IPVT = {0};
          int32_t v_LET_NON_REC_14059_n__0_OLD_K = 0;
          sisal_array_t v_LET_NON_REC_14059_n__0_OLD_LU = {0};
          sisal_array_t v_LET_NON_REC_14059_n__1_TRANS_A = {0};
          (v_LET_NON_REC_14059_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_A));
          (v_LET_NON_REC_14059_n__0_INFO = SISAL_CAST(int32_t, v_BODY_14058_n__0_p1_o));
          (v_LET_NON_REC_14059_n__0_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_p2_o));
          (v_LET_NON_REC_14059_n__0_K = SISAL_CAST(int32_t, v_BODY_14058_n__2_K));
          (v_LET_NON_REC_14059_n__0_LDA = SISAL_CAST(int32_t, v_BODY_14058_n__0_LDA));
          (v_LET_NON_REC_14059_n__0_LU = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_p5_o));
          (v_LET_NON_REC_14059_n__0_N = SISAL_CAST(int32_t, v_BODY_14058_n__0_N));
          (v_LET_NON_REC_14059_n__0_OLD_INFO = SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_INFO));
          (v_LET_NON_REC_14059_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_IPVT));
          (v_LET_NON_REC_14059_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K));
          (v_LET_NON_REC_14059_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_LU));
          (v_LET_NON_REC_14059_n__1_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14059_n__0_OLD_LU))));
          sisal_array_t v_LET_NON_REC_14059_n__2_p0_o = {0};
          (v_LET_NON_REC_14059_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14059_n__1_TRANS_A), (SISAL_CAST(int32_t, v_LET_NON_REC_14059_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14059_n__1_TRANS_A).lower_bound[0]))));
        }
        int32_t v_BODY_14058_n__8_p0_o = 0;
        (v_BODY_14058_n__8_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14058_n__0_N) - SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K))));
        int32_t v_BODY_14058_n__9_p0_o = 0;
        (v_BODY_14058_n__9_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_14058_n__10_p0_o = 0;
        (v_BODY_14058_n__10_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14058_n__8_p0_o) + SISAL_CAST(int32_t, v_BODY_14058_n__9_p0_o))));
        sisal_array_t v_BODY_14058_n__11_p0_o = {0};
        {
          sisal_array_t v_LET_NON_REC_14060_n__0_A = {0};
          int32_t v_LET_NON_REC_14060_n__0_INFO = 0;
          sisal_array_t v_LET_NON_REC_14060_n__0_IPVT = {0};
          int32_t v_LET_NON_REC_14060_n__0_K = 0;
          int32_t v_LET_NON_REC_14060_n__0_LDA = 0;
          sisal_array_t v_LET_NON_REC_14060_n__0_LU = {0};
          int32_t v_LET_NON_REC_14060_n__0_N = 0;
          int32_t v_LET_NON_REC_14060_n__0_OLD_INFO = 0;
          sisal_array_t v_LET_NON_REC_14060_n__0_OLD_IPVT = {0};
          int32_t v_LET_NON_REC_14060_n__0_OLD_K = 0;
          sisal_array_t v_LET_NON_REC_14060_n__0_OLD_LU = {0};
          sisal_array_t v_LET_NON_REC_14060_n__1_TRANS_A = {0};
          (v_LET_NON_REC_14060_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_A));
          (v_LET_NON_REC_14060_n__0_INFO = SISAL_CAST(int32_t, v_BODY_14058_n__0_p1_o));
          (v_LET_NON_REC_14060_n__0_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_p2_o));
          (v_LET_NON_REC_14060_n__0_K = SISAL_CAST(int32_t, v_BODY_14058_n__2_K));
          (v_LET_NON_REC_14060_n__0_LDA = SISAL_CAST(int32_t, v_BODY_14058_n__0_LDA));
          (v_LET_NON_REC_14060_n__0_LU = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_p5_o));
          (v_LET_NON_REC_14060_n__0_N = SISAL_CAST(int32_t, v_BODY_14058_n__0_N));
          (v_LET_NON_REC_14060_n__0_OLD_INFO = SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_INFO));
          (v_LET_NON_REC_14060_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_IPVT));
          (v_LET_NON_REC_14060_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K));
          (v_LET_NON_REC_14060_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_LU));
          (v_LET_NON_REC_14060_n__1_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14060_n__0_OLD_LU))));
          sisal_array_t v_LET_NON_REC_14060_n__2_p0_o = {0};
          (v_LET_NON_REC_14060_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14060_n__1_TRANS_A), (SISAL_CAST(int32_t, v_LET_NON_REC_14060_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14060_n__1_TRANS_A).lower_bound[0]))));
          (v_BODY_14058_n__11_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14060_n__2_p0_o));
        }
        int32_t v_BODY_14058_n__13_p0_o = 0;
        (v_BODY_14058_n__13_p0_o = SISAL_CAST(int32_t, func_ISAMAX(SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K), SISAL_CAST(int32_t, v_BODY_14058_n__10_p0_o), SISAL_CAST(sisal_array_t, v_BODY_14058_n__11_p0_o))));
        int32_t v_BODY_14058_n__14_p0_o = 0;
        (v_BODY_14058_n__14_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14058_n__13_p0_o) + SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K))));
        int32_t v_BODY_14058_n__15_p0_o = 0;
        (v_BODY_14058_n__15_p0_o = SISAL_CAST(int32_t, 1));
        (v_BODY_14058_n__16_L = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14058_n__14_p0_o) - SISAL_CAST(int32_t, v_BODY_14058_n__15_p0_o))));
        (v_BODY_14058_n__17_IPVT = SISAL_CAST(sisal_array_t, sisal_array_replace_i32(SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_IPVT), ((int64_t)SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K)), SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_BODY_14058_n__16_L)))));
        sisal_array_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_A = {0};
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_A));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_L = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_L = SISAL_CAST(int32_t, v_BODY_14058_n__16_L));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_K = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_K));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_INFO = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_INFO = SISAL_CAST(int32_t, v_BODY_14058_n__0_p1_o));
        sisal_array_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_IPVT = {0};
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14058_n__17_IPVT));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_K = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_K = SISAL_CAST(int32_t, v_BODY_14058_n__2_K));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_LDA = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_LDA = SISAL_CAST(int32_t, v_BODY_14058_n__0_LDA));
        sisal_array_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_LU = {0};
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_LU = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_p5_o));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_N = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_N = SISAL_CAST(int32_t, v_BODY_14058_n__0_N));
        int32_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_INFO = 0;
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_INFO = SISAL_CAST(int32_t, v_BODY_14058_n__0_OLD_INFO));
        sisal_array_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_IPVT = {0};
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_IPVT));
        sisal_array_t v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_LU = {0};
        (v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_BODY_14058_n__0_OLD_LU));
        {
          sisal_array_t v_PREDICATE_14062_n__0_A = {0};
          int32_t v_PREDICATE_14062_n__0_L = 0;
          int32_t v_PREDICATE_14062_n__0_OLD_K = 0;
          (v_PREDICATE_14062_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_A));
          (v_PREDICATE_14062_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_L));
          (v_PREDICATE_14062_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_K));
          sisal_array_t v_PREDICATE_14062_n__1_p0_o = {0};
          (v_PREDICATE_14062_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_14062_n__0_A), (SISAL_CAST(int32_t, v_PREDICATE_14062_n__0_L) - SISAL_CAST(sisal_array_t, v_PREDICATE_14062_n__0_A).lower_bound[0]))));
          double v_PREDICATE_14062_n__2_p0_o = 0;
          (v_PREDICATE_14062_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_14062_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_14062_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_PREDICATE_14062_n__1_p0_o).lower_bound[0])]));
          double v_PREDICATE_14062_n__3_p0_o = 0;
          (v_PREDICATE_14062_n__3_p0_o = SISAL_CAST(double, 0.));
          bool v_PREDICATE_14062_n__4_p0_o = 0;
          (v_PREDICATE_14062_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_14062_n__2_p0_o) == SISAL_CAST(double, v_PREDICATE_14062_n__3_p0_o))));
          if (v_PREDICATE_14062_n__4_p0_o) {
            int32_t v_THEN_14081_n__0_OLD_K = 0;
            sisal_array_t v_THEN_14081_n__0_OLD_LU = {0};
            (v_THEN_14081_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_K));
            (v_THEN_14081_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_LU));
            (v_BODY_14058_n__18_INFO = SISAL_CAST(int32_t, v_THEN_14081_n__0_OLD_K));
            (v_BODY_14058_n__18_LU = SISAL_CAST(sisal_array_t, v_THEN_14081_n__0_OLD_LU));
          }
          else {
            sisal_array_t v_ELSE_14063_n__0_A = {0};
            int32_t v_ELSE_14063_n__0_INFO = 0;
            sisal_array_t v_ELSE_14063_n__0_IPVT = {0};
            int32_t v_ELSE_14063_n__0_K = 0;
            int32_t v_ELSE_14063_n__0_L = 0;
            int32_t v_ELSE_14063_n__0_LDA = 0;
            sisal_array_t v_ELSE_14063_n__0_LU = {0};
            int32_t v_ELSE_14063_n__0_N = 0;
            int32_t v_ELSE_14063_n__0_OLD_INFO = 0;
            sisal_array_t v_ELSE_14063_n__0_OLD_IPVT = {0};
            int32_t v_ELSE_14063_n__0_OLD_K = 0;
            sisal_array_t v_ELSE_14063_n__0_OLD_LU = {0};
            (v_ELSE_14063_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_A));
            (v_ELSE_14063_n__0_INFO = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_INFO));
            (v_ELSE_14063_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_IPVT));
            (v_ELSE_14063_n__0_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_K));
            (v_ELSE_14063_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_L));
            (v_ELSE_14063_n__0_LDA = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_LDA));
            (v_ELSE_14063_n__0_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_LU));
            (v_ELSE_14063_n__0_N = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_N));
            (v_ELSE_14063_n__0_OLD_INFO = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_INFO));
            (v_ELSE_14063_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_IPVT));
            (v_ELSE_14063_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_K));
            (v_ELSE_14063_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE____INTEGRAL___14061_n__0_OLD_LU));
            int32_t v_ELSE_14063_n__1_p0_o = 0;
            sisal_array_t v_ELSE_14063_n__1_p1_o = {0};
            {
              sisal_array_t v_LET_NON_REC_14064_n__0_A = {0};
              sisal_array_t v_LET_NON_REC_14064_n__14_ENDLU = {0};
              int32_t v_LET_NON_REC_14064_n__0_INFO = 0;
              sisal_array_t v_LET_NON_REC_14064_n__0_IPVT = {0};
              int32_t v_LET_NON_REC_14064_n__0_K = 0;
              int32_t v_LET_NON_REC_14064_n__0_L = 0;
              int32_t v_LET_NON_REC_14064_n__0_LDA = 0;
              sisal_array_t v_LET_NON_REC_14064_n__0_LU = {0};
              int32_t v_LET_NON_REC_14064_n__0_N = 0;
              int32_t v_LET_NON_REC_14064_n__0_OLD_INFO = 0;
              sisal_array_t v_LET_NON_REC_14064_n__0_OLD_IPVT = {0};
              int32_t v_LET_NON_REC_14064_n__0_OLD_K = 0;
              sisal_array_t v_LET_NON_REC_14064_n__0_OLD_LU = {0};
              double v_LET_NON_REC_14064_n__9_T = 0;
              sisal_array_t v_LET_NON_REC_14064_n__12_T4_TRAN = {0};
              sisal_array_t v_LET_NON_REC_14064_n__2_TMP1LU = {0};
              sisal_array_t v_LET_NON_REC_14064_n__11_TMP2LU = {0};
              (v_LET_NON_REC_14064_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_14063_n__0_A));
              (v_LET_NON_REC_14064_n__0_INFO = SISAL_CAST(int32_t, v_ELSE_14063_n__0_INFO));
              (v_LET_NON_REC_14064_n__0_IPVT = SISAL_CAST(sisal_array_t, v_ELSE_14063_n__0_IPVT));
              (v_LET_NON_REC_14064_n__0_K = SISAL_CAST(int32_t, v_ELSE_14063_n__0_K));
              (v_LET_NON_REC_14064_n__0_L = SISAL_CAST(int32_t, v_ELSE_14063_n__0_L));
              (v_LET_NON_REC_14064_n__0_LDA = SISAL_CAST(int32_t, v_ELSE_14063_n__0_LDA));
              (v_LET_NON_REC_14064_n__0_LU = SISAL_CAST(sisal_array_t, v_ELSE_14063_n__0_LU));
              (v_LET_NON_REC_14064_n__0_N = SISAL_CAST(int32_t, v_ELSE_14063_n__0_N));
              (v_LET_NON_REC_14064_n__0_OLD_INFO = SISAL_CAST(int32_t, v_ELSE_14063_n__0_OLD_INFO));
              (v_LET_NON_REC_14064_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_ELSE_14063_n__0_OLD_IPVT));
              (v_LET_NON_REC_14064_n__0_OLD_K = SISAL_CAST(int32_t, v_ELSE_14063_n__0_OLD_K));
              (v_LET_NON_REC_14064_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_ELSE_14063_n__0_OLD_LU));
              sisal_array_t v_LET_NON_REC_14064_n__1_p0_o = {0};
              int32_t v_IF_array_array_dv_DOUBLE_____14065_n__0_L = 0;
              (v_IF_array_array_dv_DOUBLE_____14065_n__0_L = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_L));
              int32_t v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_K = 0;
              (v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_K = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_K));
              sisal_array_t v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_LU = {0};
              (v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_OLD_LU));
              {
                int32_t v_PREDICATE_14066_n__0_L = 0;
                int32_t v_PREDICATE_14066_n__0_OLD_K = 0;
                (v_PREDICATE_14066_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14065_n__0_L));
                (v_PREDICATE_14066_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_K));
                bool v_PREDICATE_14066_n__1_p0_o = 0;
                (v_PREDICATE_14066_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_14066_n__0_L) == SISAL_CAST(int32_t, v_PREDICATE_14066_n__0_OLD_K))));
                if (v_PREDICATE_14066_n__1_p0_o) {
                  sisal_array_t v_THEN_14068_n__0_OLD_LU = {0};
                  (v_THEN_14068_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_LU));
                  (v_LET_NON_REC_14064_n__1_p0_o = SISAL_CAST(sisal_array_t, v_THEN_14068_n__0_OLD_LU));
                }
                else {
                  int32_t v_ELSE_14067_n__0_L = 0;
                  int32_t v_ELSE_14067_n__0_OLD_K = 0;
                  sisal_array_t v_ELSE_14067_n__0_OLD_LU = {0};
                  (v_ELSE_14067_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_LU));
                  (v_ELSE_14067_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14065_n__0_L));
                  (v_ELSE_14067_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14065_n__0_OLD_K));
                  sisal_array_t v_ELSE_14067_n__1_p0_o = {0};
                  (v_ELSE_14067_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__0_OLD_LU), SISAL_CAST(int32_t, v_ELSE_14067_n__0_L))));
                  sisal_array_t v_ELSE_14067_n__2_p0_o = {0};
                  (v_ELSE_14067_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__0_OLD_LU), (SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_14067_n__0_OLD_LU).lower_bound[0]))));
                  double v_ELSE_14067_n__3_p0_o = 0;
                  (v_ELSE_14067_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_14067_n__2_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_14067_n__2_p0_o).lower_bound[0])]));
                  sisal_array_t v_ELSE_14067_n__4_p0_o = {0};
                  (v_ELSE_14067_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_ELSE_14067_n__3_p0_o)))));
                  sisal_array_t v_ELSE_14067_n__5_p0_o = {0};
                  (v_ELSE_14067_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__0_OLD_LU), SISAL_CAST(int32_t, v_ELSE_14067_n__0_L), SISAL_CAST(sisal_array_t, v_ELSE_14067_n__4_p0_o))));
                  sisal_array_t v_ELSE_14067_n__6_p0_o = {0};
                  (v_ELSE_14067_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__5_p0_o), SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K))));
                  sisal_array_t v_ELSE_14067_n__7_p0_o = {0};
                  (v_ELSE_14067_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__0_OLD_LU), (SISAL_CAST(int32_t, v_ELSE_14067_n__0_L) - SISAL_CAST(sisal_array_t, v_ELSE_14067_n__0_OLD_LU).lower_bound[0]))));
                  double v_ELSE_14067_n__8_p0_o = 0;
                  (v_ELSE_14067_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_ELSE_14067_n__7_p0_o).data)[(SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_ELSE_14067_n__7_p0_o).lower_bound[0])]));
                  sisal_array_t v_ELSE_14067_n__9_p0_o = {0};
                  (v_ELSE_14067_n__9_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__6_p0_o), ((int64_t)SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_ELSE_14067_n__8_p0_o)))));
                  sisal_array_t v_ELSE_14067_n__10_p0_o = {0};
                  (v_ELSE_14067_n__10_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_ELSE_14067_n__5_p0_o), SISAL_CAST(int32_t, v_ELSE_14067_n__0_OLD_K), SISAL_CAST(sisal_array_t, v_ELSE_14067_n__9_p0_o))));
                  (v_LET_NON_REC_14064_n__1_p0_o = SISAL_CAST(sisal_array_t, v_ELSE_14067_n__10_p0_o));
                }
              }
              double v_LET_NON_REC_14064_n__3_p0_o = 0;
              (v_LET_NON_REC_14064_n__3_p0_o = SISAL_CAST(double, 1.));
              float v_LET_NON_REC_14064_n__4_p0_o = 0;
              (v_LET_NON_REC_14064_n__4_p0_o = SISAL_CAST(float, (-SISAL_CAST(double, v_LET_NON_REC_14064_n__3_p0_o))));
              double v_LET_NON_REC_14064_n__5_p0_o = 0;
              (v_LET_NON_REC_14064_n__5_p0_o = SISAL_CAST(double, 1.));
              double v_LET_NON_REC_14064_n__6_p0_o = 0;
              (v_LET_NON_REC_14064_n__6_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_LET_NON_REC_14064_n__5_p0_o))));
              sisal_array_t v_LET_NON_REC_14064_n__7_p0_o = {0};
              (v_LET_NON_REC_14064_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__1_p0_o), (SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__1_p0_o).lower_bound[0]))));
              double v_LET_NON_REC_14064_n__8_p0_o = 0;
              (v_LET_NON_REC_14064_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__7_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__7_p0_o).lower_bound[0])]));
              (v_LET_NON_REC_14064_n__9_T = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_14064_n__6_p0_o) / SISAL_CAST(double, v_LET_NON_REC_14064_n__8_p0_o))));
              sisal_array_t v_LET_NON_REC_14064_n__10_p0_o = {0};
              {
                sisal_array_t v_LET_NON_REC_14069_n__0_A = {0};
                int32_t v_LET_NON_REC_14069_n__0_INFO = 0;
                sisal_array_t v_LET_NON_REC_14069_n__0_IPVT = {0};
                int32_t v_LET_NON_REC_14069_n__0_K = 0;
                int32_t v_LET_NON_REC_14069_n__0_L = 0;
                int32_t v_LET_NON_REC_14069_n__0_LDA = 0;
                sisal_array_t v_LET_NON_REC_14069_n__0_LU = {0};
                sisal_array_t v_LET_NON_REC_14069_n__10_MR = {0};
                int32_t v_LET_NON_REC_14069_n__0_N = 0;
                int32_t v_LET_NON_REC_14069_n__0_OLD_INFO = 0;
                sisal_array_t v_LET_NON_REC_14069_n__0_OLD_IPVT = {0};
                int32_t v_LET_NON_REC_14069_n__0_OLD_K = 0;
                sisal_array_t v_LET_NON_REC_14069_n__0_OLD_LU = {0};
                double v_LET_NON_REC_14069_n__0_T = 0;
                sisal_array_t v_LET_NON_REC_14069_n__1_T2_TRAN = {0};
                sisal_array_t v_LET_NON_REC_14069_n__0_TMP1LU = {0};
                sisal_array_t v_LET_NON_REC_14069_n__11_TMP3LU = {0};
                (v_LET_NON_REC_14069_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_A));
                (v_LET_NON_REC_14069_n__0_INFO = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_INFO));
                (v_LET_NON_REC_14069_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_IPVT));
                (v_LET_NON_REC_14069_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_K));
                (v_LET_NON_REC_14069_n__0_L = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_L));
                (v_LET_NON_REC_14069_n__0_LDA = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_LDA));
                (v_LET_NON_REC_14069_n__0_LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_LU));
                (v_LET_NON_REC_14069_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_N));
                (v_LET_NON_REC_14069_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_INFO));
                (v_LET_NON_REC_14069_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_OLD_IPVT));
                (v_LET_NON_REC_14069_n__0_OLD_K = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_K));
                (v_LET_NON_REC_14069_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_OLD_LU));
                (v_LET_NON_REC_14069_n__0_T = SISAL_CAST(double, v_LET_NON_REC_14064_n__9_T));
                (v_LET_NON_REC_14069_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__1_p0_o));
                (v_LET_NON_REC_14069_n__1_T2_TRAN = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__0_TMP1LU))));
                int32_t v_LET_NON_REC_14069_n__2_p0_o = 0;
                (v_LET_NON_REC_14069_n__2_p0_o = SISAL_CAST(int32_t, 1));
                float v_LET_NON_REC_14069_n__3_p0_o = 0;
                (v_LET_NON_REC_14069_n__3_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K) + SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__2_p0_o))));
                float v_LET_NON_REC_14069_n__4_p0_o = 0;
                (v_LET_NON_REC_14069_n__4_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_N) - SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K))));
                float v_LET_NON_REC_14069_n__5_p0_o = 0;
                (v_LET_NON_REC_14069_n__5_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__1_T2_TRAN).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__1_T2_TRAN).lower_bound[0])]));
                int32_t v_LET_NON_REC_14069_n__6_p0_o = 0;
                (v_LET_NON_REC_14069_n__6_p0_o = SISAL_CAST(int32_t, 1));
                int32_t v_LET_NON_REC_14069_n__7_p0_o = 0;
                (v_LET_NON_REC_14069_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K) + SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__6_p0_o))));
                int32_t v_LET_NON_REC_14069_n__8_p0_o = 0;
                (v_LET_NON_REC_14069_n__8_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_N) - SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K))));
                sisal_array_t v_LET_NON_REC_14069_n__9_p0_o = {0};
                (v_LET_NON_REC_14069_n__9_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__1_T2_TRAN), (SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__1_T2_TRAN).lower_bound[0]))));
                (v_LET_NON_REC_14069_n__10_MR = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__7_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__8_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__9_p0_o), SISAL_CAST(double, v_LET_NON_REC_14069_n__0_T))));
                (v_LET_NON_REC_14069_n__11_TMP3LU = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__1_T2_TRAN), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_14069_n__0_OLD_K)), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__10_MR))));
                sisal_array_t v_LET_NON_REC_14069_n__12_p0_o = {0};
                (v_LET_NON_REC_14069_n__12_p0_o = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__11_TMP3LU))));
                (v_LET_NON_REC_14064_n__10_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14069_n__12_p0_o));
              }
              (v_LET_NON_REC_14064_n__12_T4_TRAN = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__10_p0_o))));
              sisal_array_t v_LET_NON_REC_14064_n__13_p0_o = {0};
              {
                int32_t v_LoopB_14070_n__5_MERGE_J = 0;
                sisal_array_t v_LoopB_14070_n__6_MERGE_NMAT = {0};
                int32_t v_LoopB_14070_n__7_MERGE_OLD_J = 0;
                sisal_array_t v_LoopB_14070_n__8_MERGE_OLD_NMAT = {0};
                bool v_LoopB_14070_n__9_MERGE_first = 0;
                sisal_array_t v_LoopB_14070_bodycap_n3_p0 = {0};
                int32_t v_LoopB_14070_bodycap_n6_p0 = 0;
                bool v_LoopB_14070_bodycap_n7_p0 = 0;
                sisal_array_t v_LoopB_14070_n__0_A = {0};
                (v_LoopB_14070_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_A));
                int32_t v_LoopB_14070_n__0_INFO = 0;
                (v_LoopB_14070_n__0_INFO = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_INFO));
                sisal_array_t v_LoopB_14070_n__0_IPVT = {0};
                (v_LoopB_14070_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_IPVT));
                int32_t v_LoopB_14070_n__0_K = 0;
                (v_LoopB_14070_n__0_K = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_K));
                int32_t v_LoopB_14070_n__0_L = 0;
                (v_LoopB_14070_n__0_L = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_L));
                int32_t v_LoopB_14070_n__0_LDA = 0;
                (v_LoopB_14070_n__0_LDA = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_LDA));
                sisal_array_t v_LoopB_14070_n__0_LU = {0};
                (v_LoopB_14070_n__0_LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_LU));
                int32_t v_LoopB_14070_n__0_N = 0;
                (v_LoopB_14070_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_N));
                int32_t v_LoopB_14070_n__0_OLD_INFO = 0;
                (v_LoopB_14070_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_INFO));
                sisal_array_t v_LoopB_14070_n__0_OLD_IPVT = {0};
                (v_LoopB_14070_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_OLD_IPVT));
                int32_t v_LoopB_14070_n__0_OLD_K = 0;
                (v_LoopB_14070_n__0_OLD_K = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_K));
                sisal_array_t v_LoopB_14070_n__0_OLD_LU = {0};
                (v_LoopB_14070_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__0_OLD_LU));
                double v_LoopB_14070_n__0_T = 0;
                (v_LoopB_14070_n__0_T = SISAL_CAST(double, v_LET_NON_REC_14064_n__9_T));
                sisal_array_t v_LoopB_14070_n__0_T4_TRAN = {0};
                (v_LoopB_14070_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__12_T4_TRAN));
                sisal_array_t v_LoopB_14070_n__0_TMP1LU = {0};
                (v_LoopB_14070_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__1_p0_o));
                sisal_array_t v_LoopB_14070_n__0_TMP2LU = {0};
                (v_LoopB_14070_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__10_p0_o));
                sisal_array_t v_INIT_14080_n__0_A = {0};
                int32_t v_INIT_14080_n__0_INFO = 0;
                sisal_array_t v_INIT_14080_n__0_IPVT = {0};
                int32_t v_INIT_14080_n__2_J = 0;
                int32_t v_INIT_14080_n__0_K = 0;
                int32_t v_INIT_14080_n__0_L = 0;
                int32_t v_INIT_14080_n__0_LDA = 0;
                sisal_array_t v_INIT_14080_n__0_LU = {0};
                int32_t v_INIT_14080_n__0_N = 0;
                sisal_array_t v_INIT_14080_n__0_NMAT = {0};
                int32_t v_INIT_14080_n__0_OLD_INFO = 0;
                sisal_array_t v_INIT_14080_n__0_OLD_IPVT = {0};
                int32_t v_INIT_14080_n__2_OLD_J = 0;
                int32_t v_INIT_14080_n__0_OLD_K = 0;
                sisal_array_t v_INIT_14080_n__0_OLD_LU = {0};
                sisal_array_t v_INIT_14080_n__0_OLD_NMAT = {0};
                double v_INIT_14080_n__0_T = 0;
                sisal_array_t v_INIT_14080_n__0_T4_TRAN = {0};
                sisal_array_t v_INIT_14080_n__0_TMP1LU = {0};
                sisal_array_t v_INIT_14080_n__0_TMP2LU = {0};
                (v_INIT_14080_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_A));
                (v_INIT_14080_n__0_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_INFO));
                (v_INIT_14080_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_IPVT));
                (v_INIT_14080_n__0_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_K));
                (v_INIT_14080_n__0_L = SISAL_CAST(int32_t, v_LoopB_14070_n__0_L));
                (v_INIT_14080_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14070_n__0_LDA));
                (v_INIT_14080_n__0_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_LU));
                (v_INIT_14080_n__0_N = SISAL_CAST(int32_t, v_LoopB_14070_n__0_N));
                (v_INIT_14080_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_INFO));
                (v_INIT_14080_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_IPVT));
                (v_INIT_14080_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_K));
                (v_INIT_14080_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_LU));
                (v_INIT_14080_n__0_T = SISAL_CAST(double, v_LoopB_14070_n__0_T));
                (v_INIT_14080_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_T4_TRAN));
                (v_INIT_14080_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP1LU));
                (v_INIT_14080_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP2LU));
                int32_t v_INIT_14080_n__1_p0_o = 0;
                (v_INIT_14080_n__1_p0_o = SISAL_CAST(int32_t, 1));
                (v_INIT_14080_n__2_OLD_J = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_INIT_14080_n__0_OLD_K) + SISAL_CAST(int32_t, v_INIT_14080_n__1_p0_o))));
                bool v_INIT_14080_n__3_p0_o = 0;
                (v_INIT_14080_n__3_p0_o = SISAL_CAST(bool, true));
                (v_LoopB_14070_n__5_MERGE_J = v_INIT_14080_n__2_OLD_J);
                (v_LoopB_14070_n__6_MERGE_NMAT = v_INIT_14080_n__0_T4_TRAN);
                (v_LoopB_14070_n__7_MERGE_OLD_J = v_INIT_14080_n__2_OLD_J);
                (v_LoopB_14070_n__8_MERGE_OLD_NMAT = v_INIT_14080_n__0_T4_TRAN);
                (v_LoopB_14070_n__9_MERGE_first = v_INIT_14080_n__3_p0_o);
                sisal_array_t v_TEST_14079_n__0_A = {0};
                int32_t v_TEST_14079_n__0_INFO = 0;
                sisal_array_t v_TEST_14079_n__0_IPVT = {0};
                int32_t v_TEST_14079_n__0_J = 0;
                int32_t v_TEST_14079_n__0_K = 0;
                int32_t v_TEST_14079_n__0_L = 0;
                int32_t v_TEST_14079_n__0_LDA = 0;
                sisal_array_t v_TEST_14079_n__0_LU = {0};
                int32_t v_TEST_14079_n__0_N = 0;
                sisal_array_t v_TEST_14079_n__0_NMAT = {0};
                int32_t v_TEST_14079_n__0_OLD_INFO = 0;
                sisal_array_t v_TEST_14079_n__0_OLD_IPVT = {0};
                int32_t v_TEST_14079_n__0_OLD_J = 0;
                int32_t v_TEST_14079_n__0_OLD_K = 0;
                sisal_array_t v_TEST_14079_n__0_OLD_LU = {0};
                sisal_array_t v_TEST_14079_n__0_OLD_NMAT = {0};
                double v_TEST_14079_n__0_T = 0;
                sisal_array_t v_TEST_14079_n__0_T4_TRAN = {0};
                sisal_array_t v_TEST_14079_n__0_TMP1LU = {0};
                sisal_array_t v_TEST_14079_n__0_TMP2LU = {0};
                (v_TEST_14079_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_A));
                (v_TEST_14079_n__0_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_INFO));
                (v_TEST_14079_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_IPVT));
                (v_TEST_14079_n__0_J = SISAL_CAST(int32_t, v_LoopB_14070_n__5_MERGE_J));
                (v_TEST_14079_n__0_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_K));
                (v_TEST_14079_n__0_L = SISAL_CAST(int32_t, v_LoopB_14070_n__0_L));
                (v_TEST_14079_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14070_n__0_LDA));
                (v_TEST_14079_n__0_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_LU));
                (v_TEST_14079_n__0_N = SISAL_CAST(int32_t, v_LoopB_14070_n__0_N));
                (v_TEST_14079_n__0_NMAT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__6_MERGE_NMAT));
                (v_TEST_14079_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_INFO));
                (v_TEST_14079_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_IPVT));
                (v_TEST_14079_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_14070_n__7_MERGE_OLD_J));
                (v_TEST_14079_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_K));
                (v_TEST_14079_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_LU));
                (v_TEST_14079_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__8_MERGE_OLD_NMAT));
                (v_TEST_14079_n__0_T = SISAL_CAST(double, v_LoopB_14070_n__0_T));
                (v_TEST_14079_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_T4_TRAN));
                (v_TEST_14079_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP1LU));
                (v_TEST_14079_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP2LU));
                bool v_TEST_14079_n__1_p0_o = 0;
                (v_TEST_14079_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_14079_n__0_J) <= SISAL_CAST(int32_t, v_TEST_14079_n__0_N))));
                #ifdef SISAL_TRAP_ZERO_TRIP
                if ((!v_TEST_14079_n__1_p0_o)) {
                  fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_14070 executed 0 times (guard false on entry)\n");
                  exit(1);
                }
                #endif
                while (v_TEST_14079_n__1_p0_o) {
                  sisal_array_t v_BODY_14071_n__0_A = {0};
                  int32_t v_BODY_14071_n__0_INFO = 0;
                  sisal_array_t v_BODY_14071_n__0_IPVT = {0};
                  int32_t v_BODY_14071_n__6_J = 0;
                  int32_t v_BODY_14071_n__0_K = 0;
                  int32_t v_BODY_14071_n__0_L = 0;
                  int32_t v_BODY_14071_n__0_LDA = 0;
                  sisal_array_t v_BODY_14071_n__0_LU = {0};
                  int32_t v_BODY_14071_n__0_N = 0;
                  sisal_array_t v_BODY_14071_n__3_NMAT = {0};
                  int32_t v_BODY_14071_n__0_OLD_INFO = 0;
                  sisal_array_t v_BODY_14071_n__0_OLD_IPVT = {0};
                  int32_t v_BODY_14071_n__0_OLD_J = 0;
                  int32_t v_BODY_14071_n__0_OLD_K = 0;
                  sisal_array_t v_BODY_14071_n__0_OLD_LU = {0};
                  sisal_array_t v_BODY_14071_n__0_OLD_NMAT = {0};
                  double v_BODY_14071_n__2_T = 0;
                  sisal_array_t v_BODY_14071_n__0_T4_TRAN = {0};
                  sisal_array_t v_BODY_14071_n__0_TMP1LU = {0};
                  sisal_array_t v_BODY_14071_n__0_TMP2LU = {0};
                  int32_t v_BODY_14071_n__0_p3_o = 0;
                  sisal_array_t v_BODY_14071_n__0_p9_o = {0};
                  (v_BODY_14071_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_A));
                  (v_BODY_14071_n__0_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_INFO));
                  (v_BODY_14071_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_IPVT));
                  (v_BODY_14071_n__0_p3_o = SISAL_CAST(int32_t, v_LoopB_14070_n__5_MERGE_J));
                  (v_BODY_14071_n__0_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_K));
                  (v_BODY_14071_n__0_L = SISAL_CAST(int32_t, v_LoopB_14070_n__0_L));
                  (v_BODY_14071_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14070_n__0_LDA));
                  (v_BODY_14071_n__0_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_LU));
                  (v_BODY_14071_n__0_N = SISAL_CAST(int32_t, v_LoopB_14070_n__0_N));
                  (v_BODY_14071_n__0_p9_o = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__6_MERGE_NMAT));
                  (v_BODY_14071_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_INFO));
                  (v_BODY_14071_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_IPVT));
                  (v_BODY_14071_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_14070_n__7_MERGE_OLD_J));
                  (v_BODY_14071_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_K));
                  (v_BODY_14071_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_LU));
                  (v_BODY_14071_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__8_MERGE_OLD_NMAT));
                  double v_BODY_14071_n__0_p16_o = 0;
                  (v_BODY_14071_n__0_p16_o = SISAL_CAST(double, v_LoopB_14070_n__0_T));
                  (v_BODY_14071_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_T4_TRAN));
                  (v_BODY_14071_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP1LU));
                  (v_BODY_14071_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP2LU));
                  sisal_array_t v_BODY_14071_n__1_p0_o = {0};
                  (v_BODY_14071_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_OLD_NMAT), (SISAL_CAST(int32_t, v_BODY_14071_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_OLD_NMAT).lower_bound[0]))));
                  (v_BODY_14071_n__2_T = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_14071_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_14071_n__0_L) - SISAL_CAST(sisal_array_t, v_BODY_14071_n__1_p0_o).lower_bound[0])]));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_L = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_L = SISAL_CAST(int32_t, v_BODY_14071_n__0_L));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_K = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_14071_n__0_OLD_K));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_A = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_A));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_INFO = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_INFO = SISAL_CAST(int32_t, v_BODY_14071_n__0_INFO));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_IPVT = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_IPVT));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_J = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_J = SISAL_CAST(int32_t, v_BODY_14071_n__0_p3_o));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_K = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_K = SISAL_CAST(int32_t, v_BODY_14071_n__0_K));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_LDA = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_LDA = SISAL_CAST(int32_t, v_BODY_14071_n__0_LDA));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_LU = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_LU = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_LU));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_N = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_N = SISAL_CAST(int32_t, v_BODY_14071_n__0_N));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_NMAT = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_NMAT = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_p9_o));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_INFO = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_INFO = SISAL_CAST(int32_t, v_BODY_14071_n__0_OLD_INFO));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_IPVT = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_OLD_IPVT));
                  int32_t v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_J = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_J = SISAL_CAST(int32_t, v_BODY_14071_n__0_OLD_J));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_LU = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_OLD_LU));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_NMAT = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_OLD_NMAT));
                  double v_IF_array_array_dv_DOUBLE_____14072_n__0_T = 0;
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_T = SISAL_CAST(double, v_BODY_14071_n__2_T));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_T4_TRAN = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_T4_TRAN));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP1LU = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_TMP1LU));
                  sisal_array_t v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP2LU = {0};
                  (v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_BODY_14071_n__0_TMP2LU));
                  {
                    int32_t v_PREDICATE_14073_n__0_L = 0;
                    int32_t v_PREDICATE_14073_n__0_OLD_K = 0;
                    (v_PREDICATE_14073_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_L));
                    (v_PREDICATE_14073_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_K));
                    bool v_PREDICATE_14073_n__1_p0_o = 0;
                    (v_PREDICATE_14073_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_14073_n__0_L) == SISAL_CAST(int32_t, v_PREDICATE_14073_n__0_OLD_K))));
                    if (v_PREDICATE_14073_n__1_p0_o) {
                      sisal_array_t v_THEN_14076_n__0_A = {0};
                      int32_t v_THEN_14076_n__0_INFO = 0;
                      sisal_array_t v_THEN_14076_n__0_IPVT = {0};
                      int32_t v_THEN_14076_n__0_J = 0;
                      int32_t v_THEN_14076_n__0_K = 0;
                      int32_t v_THEN_14076_n__0_L = 0;
                      int32_t v_THEN_14076_n__0_LDA = 0;
                      sisal_array_t v_THEN_14076_n__0_LU = {0};
                      int32_t v_THEN_14076_n__0_N = 0;
                      sisal_array_t v_THEN_14076_n__0_NMAT = {0};
                      int32_t v_THEN_14076_n__0_OLD_INFO = 0;
                      sisal_array_t v_THEN_14076_n__0_OLD_IPVT = {0};
                      int32_t v_THEN_14076_n__0_OLD_J = 0;
                      int32_t v_THEN_14076_n__0_OLD_K = 0;
                      sisal_array_t v_THEN_14076_n__0_OLD_LU = {0};
                      sisal_array_t v_THEN_14076_n__0_OLD_NMAT = {0};
                      double v_THEN_14076_n__0_T = 0;
                      sisal_array_t v_THEN_14076_n__0_T4_TRAN = {0};
                      sisal_array_t v_THEN_14076_n__0_TMP1LU = {0};
                      sisal_array_t v_THEN_14076_n__0_TMP2LU = {0};
                      (v_THEN_14076_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_A));
                      (v_THEN_14076_n__0_INFO = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_INFO));
                      (v_THEN_14076_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_IPVT));
                      (v_THEN_14076_n__0_J = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_J));
                      (v_THEN_14076_n__0_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_K));
                      (v_THEN_14076_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_L));
                      (v_THEN_14076_n__0_LDA = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_LDA));
                      (v_THEN_14076_n__0_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_LU));
                      (v_THEN_14076_n__0_N = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_N));
                      (v_THEN_14076_n__0_NMAT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_NMAT));
                      (v_THEN_14076_n__0_OLD_INFO = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_INFO));
                      (v_THEN_14076_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_IPVT));
                      (v_THEN_14076_n__0_OLD_J = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_J));
                      (v_THEN_14076_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_K));
                      (v_THEN_14076_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_LU));
                      (v_THEN_14076_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_NMAT));
                      (v_THEN_14076_n__0_T = SISAL_CAST(double, v_IF_array_array_dv_DOUBLE_____14072_n__0_T));
                      (v_THEN_14076_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_T4_TRAN));
                      (v_THEN_14076_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP1LU));
                      (v_THEN_14076_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP2LU));
                      sisal_array_t v_THEN_14076_n__1_p0_o = {0};
                      {
                        sisal_array_t v_LET_NON_REC_14077_n__0_A = {0};
                        int32_t v_LET_NON_REC_14077_n__0_INFO = 0;
                        sisal_array_t v_LET_NON_REC_14077_n__0_IPVT = {0};
                        int32_t v_LET_NON_REC_14077_n__0_J = 0;
                        int32_t v_LET_NON_REC_14077_n__0_K = 0;
                        int32_t v_LET_NON_REC_14077_n__0_L = 0;
                        int32_t v_LET_NON_REC_14077_n__0_LDA = 0;
                        sisal_array_t v_LET_NON_REC_14077_n__0_LU = {0};
                        int32_t v_LET_NON_REC_14077_n__0_N = 0;
                        sisal_array_t v_LET_NON_REC_14077_n__0_NMAT = {0};
                        sisal_array_t v_LET_NON_REC_14077_n__11_NROW = {0};
                        int32_t v_LET_NON_REC_14077_n__0_OLD_INFO = 0;
                        sisal_array_t v_LET_NON_REC_14077_n__0_OLD_IPVT = {0};
                        int32_t v_LET_NON_REC_14077_n__0_OLD_J = 0;
                        int32_t v_LET_NON_REC_14077_n__0_OLD_K = 0;
                        sisal_array_t v_LET_NON_REC_14077_n__0_OLD_LU = {0};
                        sisal_array_t v_LET_NON_REC_14077_n__0_OLD_NMAT = {0};
                        double v_LET_NON_REC_14077_n__0_T = 0;
                        sisal_array_t v_LET_NON_REC_14077_n__0_T4_TRAN = {0};
                        sisal_array_t v_LET_NON_REC_14077_n__0_TMP1LU = {0};
                        sisal_array_t v_LET_NON_REC_14077_n__0_TMP2LU = {0};
                        (v_LET_NON_REC_14077_n__0_A = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_A));
                        (v_LET_NON_REC_14077_n__0_INFO = SISAL_CAST(int32_t, v_THEN_14076_n__0_INFO));
                        (v_LET_NON_REC_14077_n__0_IPVT = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_IPVT));
                        (v_LET_NON_REC_14077_n__0_J = SISAL_CAST(int32_t, v_THEN_14076_n__0_J));
                        (v_LET_NON_REC_14077_n__0_K = SISAL_CAST(int32_t, v_THEN_14076_n__0_K));
                        (v_LET_NON_REC_14077_n__0_L = SISAL_CAST(int32_t, v_THEN_14076_n__0_L));
                        (v_LET_NON_REC_14077_n__0_LDA = SISAL_CAST(int32_t, v_THEN_14076_n__0_LDA));
                        (v_LET_NON_REC_14077_n__0_LU = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_LU));
                        (v_LET_NON_REC_14077_n__0_N = SISAL_CAST(int32_t, v_THEN_14076_n__0_N));
                        (v_LET_NON_REC_14077_n__0_NMAT = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_NMAT));
                        (v_LET_NON_REC_14077_n__0_OLD_INFO = SISAL_CAST(int32_t, v_THEN_14076_n__0_OLD_INFO));
                        (v_LET_NON_REC_14077_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_OLD_IPVT));
                        (v_LET_NON_REC_14077_n__0_OLD_J = SISAL_CAST(int32_t, v_THEN_14076_n__0_OLD_J));
                        (v_LET_NON_REC_14077_n__0_OLD_K = SISAL_CAST(int32_t, v_THEN_14076_n__0_OLD_K));
                        (v_LET_NON_REC_14077_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_OLD_LU));
                        (v_LET_NON_REC_14077_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_OLD_NMAT));
                        (v_LET_NON_REC_14077_n__0_T = SISAL_CAST(double, v_THEN_14076_n__0_T));
                        (v_LET_NON_REC_14077_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_T4_TRAN));
                        (v_LET_NON_REC_14077_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_TMP1LU));
                        (v_LET_NON_REC_14077_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_THEN_14076_n__0_TMP2LU));
                        int32_t v_LET_NON_REC_14077_n__1_p0_o = 0;
                        (v_LET_NON_REC_14077_n__1_p0_o = SISAL_CAST(int32_t, 1));
                        float v_LET_NON_REC_14077_n__2_p0_o = 0;
                        (v_LET_NON_REC_14077_n__2_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_K) + SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__1_p0_o))));
                        float v_LET_NON_REC_14077_n__3_p0_o = 0;
                        (v_LET_NON_REC_14077_n__3_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_N) - SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_K))));
                        float v_LET_NON_REC_14077_n__4_p0_o = 0;
                        (v_LET_NON_REC_14077_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT).lower_bound[0])]));
                        float v_LET_NON_REC_14077_n__5_p0_o = 0;
                        (v_LET_NON_REC_14077_n__5_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT).lower_bound[0])]));
                        int32_t v_LET_NON_REC_14077_n__6_p0_o = 0;
                        (v_LET_NON_REC_14077_n__6_p0_o = SISAL_CAST(int32_t, 1));
                        int32_t v_LET_NON_REC_14077_n__7_p0_o = 0;
                        (v_LET_NON_REC_14077_n__7_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_K) + SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__6_p0_o))));
                        int32_t v_LET_NON_REC_14077_n__8_p0_o = 0;
                        (v_LET_NON_REC_14077_n__8_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_N) - SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_K))));
                        sisal_array_t v_LET_NON_REC_14077_n__9_p0_o = {0};
                        (v_LET_NON_REC_14077_n__9_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT), (SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT).lower_bound[0]))));
                        sisal_array_t v_LET_NON_REC_14077_n__10_p0_o = {0};
                        (v_LET_NON_REC_14077_n__10_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT), (SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT).lower_bound[0]))));
                        (v_LET_NON_REC_14077_n__11_NROW = SISAL_CAST(sisal_array_t, func_SAXPY(SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__7_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__8_p0_o), SISAL_CAST(double, v_LET_NON_REC_14077_n__0_T), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__9_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__10_p0_o))));
                        sisal_array_t v_LET_NON_REC_14077_n__12_p0_o = {0};
                        (v_LET_NON_REC_14077_n__12_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__0_OLD_NMAT), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_14077_n__0_OLD_J)), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__11_NROW))));
                        (v_THEN_14076_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14077_n__12_p0_o));
                      }
                      (v_BODY_14071_n__3_NMAT = SISAL_CAST(sisal_array_t, v_THEN_14076_n__1_p0_o));
                    }
                    else {
                      sisal_array_t v_ELSE_14074_n__0_A = {0};
                      int32_t v_ELSE_14074_n__0_INFO = 0;
                      sisal_array_t v_ELSE_14074_n__0_IPVT = {0};
                      int32_t v_ELSE_14074_n__0_J = 0;
                      int32_t v_ELSE_14074_n__0_K = 0;
                      int32_t v_ELSE_14074_n__0_L = 0;
                      int32_t v_ELSE_14074_n__0_LDA = 0;
                      sisal_array_t v_ELSE_14074_n__0_LU = {0};
                      int32_t v_ELSE_14074_n__0_N = 0;
                      sisal_array_t v_ELSE_14074_n__0_NMAT = {0};
                      int32_t v_ELSE_14074_n__0_OLD_INFO = 0;
                      sisal_array_t v_ELSE_14074_n__0_OLD_IPVT = {0};
                      int32_t v_ELSE_14074_n__0_OLD_J = 0;
                      int32_t v_ELSE_14074_n__0_OLD_K = 0;
                      sisal_array_t v_ELSE_14074_n__0_OLD_LU = {0};
                      sisal_array_t v_ELSE_14074_n__0_OLD_NMAT = {0};
                      double v_ELSE_14074_n__0_T = 0;
                      sisal_array_t v_ELSE_14074_n__0_T4_TRAN = {0};
                      sisal_array_t v_ELSE_14074_n__0_TMP1LU = {0};
                      sisal_array_t v_ELSE_14074_n__0_TMP2LU = {0};
                      (v_ELSE_14074_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_A));
                      (v_ELSE_14074_n__0_INFO = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_INFO));
                      (v_ELSE_14074_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_IPVT));
                      (v_ELSE_14074_n__0_J = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_J));
                      (v_ELSE_14074_n__0_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_K));
                      (v_ELSE_14074_n__0_L = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_L));
                      (v_ELSE_14074_n__0_LDA = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_LDA));
                      (v_ELSE_14074_n__0_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_LU));
                      (v_ELSE_14074_n__0_N = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_N));
                      (v_ELSE_14074_n__0_NMAT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_NMAT));
                      (v_ELSE_14074_n__0_OLD_INFO = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_INFO));
                      (v_ELSE_14074_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_IPVT));
                      (v_ELSE_14074_n__0_OLD_J = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_J));
                      (v_ELSE_14074_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_K));
                      (v_ELSE_14074_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_LU));
                      (v_ELSE_14074_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_OLD_NMAT));
                      (v_ELSE_14074_n__0_T = SISAL_CAST(double, v_IF_array_array_dv_DOUBLE_____14072_n__0_T));
                      (v_ELSE_14074_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_T4_TRAN));
                      (v_ELSE_14074_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP1LU));
                      (v_ELSE_14074_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_IF_array_array_dv_DOUBLE_____14072_n__0_TMP2LU));
                      sisal_array_t v_ELSE_14074_n__1_p0_o = {0};
                      {
                        sisal_array_t v_LET_NON_REC_14075_n__0_A = {0};
                        sisal_array_t v_LET_NON_REC_14075_n__10_DUMMAT = {0};
                        sisal_array_t v_LET_NON_REC_14075_n__21_DUMROW = {0};
                        int32_t v_LET_NON_REC_14075_n__0_INFO = 0;
                        sisal_array_t v_LET_NON_REC_14075_n__0_IPVT = {0};
                        int32_t v_LET_NON_REC_14075_n__0_J = 0;
                        int32_t v_LET_NON_REC_14075_n__0_K = 0;
                        int32_t v_LET_NON_REC_14075_n__0_L = 0;
                        int32_t v_LET_NON_REC_14075_n__0_LDA = 0;
                        sisal_array_t v_LET_NON_REC_14075_n__0_LU = {0};
                        int32_t v_LET_NON_REC_14075_n__0_N = 0;
                        sisal_array_t v_LET_NON_REC_14075_n__0_NMAT = {0};
                        int32_t v_LET_NON_REC_14075_n__0_OLD_INFO = 0;
                        sisal_array_t v_LET_NON_REC_14075_n__0_OLD_IPVT = {0};
                        int32_t v_LET_NON_REC_14075_n__0_OLD_J = 0;
                        int32_t v_LET_NON_REC_14075_n__0_OLD_K = 0;
                        sisal_array_t v_LET_NON_REC_14075_n__0_OLD_LU = {0};
                        sisal_array_t v_LET_NON_REC_14075_n__0_OLD_NMAT = {0};
                        double v_LET_NON_REC_14075_n__0_T = 0;
                        sisal_array_t v_LET_NON_REC_14075_n__0_T4_TRAN = {0};
                        sisal_array_t v_LET_NON_REC_14075_n__0_TMP1LU = {0};
                        sisal_array_t v_LET_NON_REC_14075_n__0_TMP2LU = {0};
                        (v_LET_NON_REC_14075_n__0_A = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_A));
                        (v_LET_NON_REC_14075_n__0_INFO = SISAL_CAST(int32_t, v_ELSE_14074_n__0_INFO));
                        (v_LET_NON_REC_14075_n__0_IPVT = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_IPVT));
                        (v_LET_NON_REC_14075_n__0_J = SISAL_CAST(int32_t, v_ELSE_14074_n__0_J));
                        (v_LET_NON_REC_14075_n__0_K = SISAL_CAST(int32_t, v_ELSE_14074_n__0_K));
                        (v_LET_NON_REC_14075_n__0_L = SISAL_CAST(int32_t, v_ELSE_14074_n__0_L));
                        (v_LET_NON_REC_14075_n__0_LDA = SISAL_CAST(int32_t, v_ELSE_14074_n__0_LDA));
                        (v_LET_NON_REC_14075_n__0_LU = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_LU));
                        (v_LET_NON_REC_14075_n__0_N = SISAL_CAST(int32_t, v_ELSE_14074_n__0_N));
                        (v_LET_NON_REC_14075_n__0_NMAT = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_NMAT));
                        (v_LET_NON_REC_14075_n__0_OLD_INFO = SISAL_CAST(int32_t, v_ELSE_14074_n__0_OLD_INFO));
                        (v_LET_NON_REC_14075_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_OLD_IPVT));
                        (v_LET_NON_REC_14075_n__0_OLD_J = SISAL_CAST(int32_t, v_ELSE_14074_n__0_OLD_J));
                        (v_LET_NON_REC_14075_n__0_OLD_K = SISAL_CAST(int32_t, v_ELSE_14074_n__0_OLD_K));
                        (v_LET_NON_REC_14075_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_OLD_LU));
                        (v_LET_NON_REC_14075_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_OLD_NMAT));
                        (v_LET_NON_REC_14075_n__0_T = SISAL_CAST(double, v_ELSE_14074_n__0_T));
                        (v_LET_NON_REC_14075_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_T4_TRAN));
                        (v_LET_NON_REC_14075_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_TMP1LU));
                        (v_LET_NON_REC_14075_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__0_TMP2LU));
                        sisal_array_t v_LET_NON_REC_14075_n__1_p0_o = {0};
                        (v_LET_NON_REC_14075_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__0_OLD_NMAT), SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J))));
                        sisal_array_t v_LET_NON_REC_14075_n__2_p0_o = {0};
                        (v_LET_NON_REC_14075_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__0_OLD_NMAT), (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__0_OLD_NMAT).lower_bound[0]))));
                        double v_LET_NON_REC_14075_n__3_p0_o = 0;
                        (v_LET_NON_REC_14075_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__2_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__2_p0_o).lower_bound[0])]));
                        sisal_array_t v_LET_NON_REC_14075_n__4_p0_o = {0};
                        (v_LET_NON_REC_14075_n__4_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__1_p0_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_L)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_14075_n__3_p0_o)))));
                        sisal_array_t v_LET_NON_REC_14075_n__5_p0_o = {0};
                        (v_LET_NON_REC_14075_n__5_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__0_OLD_NMAT), SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__4_p0_o))));
                        sisal_array_t v_LET_NON_REC_14075_n__6_p0_o = {0};
                        (v_LET_NON_REC_14075_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_rank_reduce(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__5_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J))));
                        sisal_array_t v_LET_NON_REC_14075_n__7_p0_o = {0};
                        (v_LET_NON_REC_14075_n__7_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__0_OLD_NMAT), (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__0_OLD_NMAT).lower_bound[0]))));
                        double v_LET_NON_REC_14075_n__8_p0_o = 0;
                        (v_LET_NON_REC_14075_n__8_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__7_p0_o).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_L) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__7_p0_o).lower_bound[0])]));
                        sisal_array_t v_LET_NON_REC_14075_n__9_p0_o = {0};
                        (v_LET_NON_REC_14075_n__9_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__6_p0_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_LET_NON_REC_14075_n__8_p0_o)))));
                        (v_LET_NON_REC_14075_n__10_DUMMAT = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__5_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__9_p0_o))));
                        int32_t v_LET_NON_REC_14075_n__11_p0_o = 0;
                        (v_LET_NON_REC_14075_n__11_p0_o = SISAL_CAST(int32_t, 1));
                        float v_LET_NON_REC_14075_n__12_p0_o = 0;
                        (v_LET_NON_REC_14075_n__12_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K) + SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__11_p0_o))));
                        float v_LET_NON_REC_14075_n__13_p0_o = 0;
                        (v_LET_NON_REC_14075_n__13_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_N) - SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K))));
                        float v_LET_NON_REC_14075_n__14_p0_o = 0;
                        (v_LET_NON_REC_14075_n__14_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT).lower_bound[0])]));
                        float v_LET_NON_REC_14075_n__15_p0_o = 0;
                        (v_LET_NON_REC_14075_n__15_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT).data)[(SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT).lower_bound[0])]));
                        int32_t v_LET_NON_REC_14075_n__16_p0_o = 0;
                        (v_LET_NON_REC_14075_n__16_p0_o = SISAL_CAST(int32_t, 1));
                        int32_t v_LET_NON_REC_14075_n__17_p0_o = 0;
                        (v_LET_NON_REC_14075_n__17_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K) + SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__16_p0_o))));
                        int32_t v_LET_NON_REC_14075_n__18_p0_o = 0;
                        (v_LET_NON_REC_14075_n__18_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_N) - SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K))));
                        sisal_array_t v_LET_NON_REC_14075_n__19_p0_o = {0};
                        (v_LET_NON_REC_14075_n__19_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT), (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT).lower_bound[0]))));
                        sisal_array_t v_LET_NON_REC_14075_n__20_p0_o = {0};
                        (v_LET_NON_REC_14075_n__20_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT), (SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT).lower_bound[0]))));
                        (v_LET_NON_REC_14075_n__21_DUMROW = SISAL_CAST(sisal_array_t, func_SAXPY(SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__17_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__18_p0_o), SISAL_CAST(double, v_LET_NON_REC_14075_n__0_T), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__19_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__20_p0_o))));
                        sisal_array_t v_LET_NON_REC_14075_n__22_p0_o = {0};
                        (v_LET_NON_REC_14075_n__22_p0_o = SISAL_CAST(sisal_array_t, sisal_dv_replace_slice(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__10_DUMMAT), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_14075_n__0_OLD_J)), SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__21_DUMROW))));
                        (v_ELSE_14074_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14075_n__22_p0_o));
                      }
                      (v_BODY_14071_n__3_NMAT = SISAL_CAST(sisal_array_t, v_ELSE_14074_n__1_p0_o));
                    }
                  }
                  int32_t v_BODY_14071_n__5_p0_o = 0;
                  (v_BODY_14071_n__5_p0_o = SISAL_CAST(int32_t, 1));
                  (v_BODY_14071_n__6_J = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_14071_n__0_OLD_J) + SISAL_CAST(int32_t, v_BODY_14071_n__5_p0_o))));
                  bool v_BODY_14071_n__7_p0_o = 0;
                  (v_BODY_14071_n__7_p0_o = SISAL_CAST(bool, false));
                  (v_LoopB_14070_bodycap_n3_p0 = v_BODY_14071_n__3_NMAT);
                  (v_LoopB_14070_bodycap_n6_p0 = v_BODY_14071_n__6_J);
                  (v_LoopB_14070_bodycap_n7_p0 = v_BODY_14071_n__7_p0_o);
                  (v_LoopB_14070_n__5_MERGE_J = v_LoopB_14070_bodycap_n6_p0);
                  (v_LoopB_14070_n__6_MERGE_NMAT = v_LoopB_14070_bodycap_n3_p0);
                  (v_LoopB_14070_n__7_MERGE_OLD_J = v_LoopB_14070_bodycap_n6_p0);
                  (v_LoopB_14070_n__8_MERGE_OLD_NMAT = v_LoopB_14070_bodycap_n3_p0);
                  (v_LoopB_14070_n__9_MERGE_first = v_LoopB_14070_bodycap_n7_p0);
                  (v_TEST_14079_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_A));
                  (v_TEST_14079_n__0_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_INFO));
                  (v_TEST_14079_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_IPVT));
                  (v_TEST_14079_n__0_J = SISAL_CAST(int32_t, v_LoopB_14070_n__5_MERGE_J));
                  (v_TEST_14079_n__0_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_K));
                  (v_TEST_14079_n__0_L = SISAL_CAST(int32_t, v_LoopB_14070_n__0_L));
                  (v_TEST_14079_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14070_n__0_LDA));
                  (v_TEST_14079_n__0_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_LU));
                  (v_TEST_14079_n__0_N = SISAL_CAST(int32_t, v_LoopB_14070_n__0_N));
                  (v_TEST_14079_n__0_NMAT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__6_MERGE_NMAT));
                  (v_TEST_14079_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_INFO));
                  (v_TEST_14079_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_IPVT));
                  (v_TEST_14079_n__0_OLD_J = SISAL_CAST(int32_t, v_LoopB_14070_n__7_MERGE_OLD_J));
                  (v_TEST_14079_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14070_n__0_OLD_K));
                  (v_TEST_14079_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_OLD_LU));
                  (v_TEST_14079_n__0_OLD_NMAT = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__8_MERGE_OLD_NMAT));
                  (v_TEST_14079_n__0_T = SISAL_CAST(double, v_LoopB_14070_n__0_T));
                  (v_TEST_14079_n__0_T4_TRAN = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_T4_TRAN));
                  (v_TEST_14079_n__0_TMP1LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP1LU));
                  (v_TEST_14079_n__0_TMP2LU = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__0_TMP2LU));
                  (v_TEST_14079_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_14079_n__0_J) <= SISAL_CAST(int32_t, v_TEST_14079_n__0_N))));
                }
                sisal_array_t v_RETURNS_14078_n__0_p0_o = {0};
                (v_RETURNS_14078_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_14070_n__8_MERGE_OLD_NMAT));
                sisal_array_t v_RETURNS_14078_n__1_p0_o = {0};
                (v_RETURNS_14078_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_14078_n__0_p0_o)));
                (v_LET_NON_REC_14064_n__13_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_14078_n__1_p0_o));
              }
              sisal_array_t v_LET_NON_REC_14064_n__15_p0_o = {0};
              (v_LET_NON_REC_14064_n__15_p0_o = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__13_p0_o))));
              (v_ELSE_14063_n__1_p0_o = SISAL_CAST(int32_t, v_LET_NON_REC_14064_n__0_OLD_INFO));
              (v_ELSE_14063_n__1_p1_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14064_n__15_p0_o));
            }
            (v_BODY_14058_n__18_INFO = SISAL_CAST(int32_t, v_ELSE_14063_n__1_p0_o));
            (v_BODY_14058_n__18_LU = SISAL_CAST(sisal_array_t, v_ELSE_14063_n__1_p1_o));
          }
        }
        bool v_BODY_14058_n__20_p0_o = 0;
        (v_BODY_14058_n__20_p0_o = SISAL_CAST(bool, false));
        (v_LoopB_14057_bodycap_n2_p0 = v_BODY_14058_n__2_K);
        (v_LoopB_14057_bodycap_n17_p0 = v_BODY_14058_n__17_IPVT);
        (v_LoopB_14057_bodycap_n18_p0 = v_BODY_14058_n__18_INFO);
        (v_LoopB_14057_bodycap_n18_p1 = v_BODY_14058_n__18_LU);
        (v_LoopB_14057_bodycap_n20_p0 = v_BODY_14058_n__20_p0_o);
        (v_LoopB_14057_n__5_MERGE_INFO = v_LoopB_14057_bodycap_n18_p0);
        (v_LoopB_14057_n__6_MERGE_IPVT = v_LoopB_14057_bodycap_n17_p0);
        (v_LoopB_14057_n__7_MERGE_K = v_LoopB_14057_bodycap_n2_p0);
        (v_LoopB_14057_n__8_MERGE_LU = v_LoopB_14057_bodycap_n18_p1);
        (v_LoopB_14057_n__9_MERGE_OLD_INFO = v_LoopB_14057_bodycap_n18_p0);
        (v_LoopB_14057_n__10_MERGE_OLD_IPVT = v_LoopB_14057_bodycap_n17_p0);
        (v_LoopB_14057_n__11_MERGE_OLD_K = v_LoopB_14057_bodycap_n2_p0);
        (v_LoopB_14057_n__12_MERGE_OLD_LU = v_LoopB_14057_bodycap_n18_p1);
        (v_LoopB_14057_n__13_MERGE_first = v_LoopB_14057_bodycap_n20_p0);
        (v_TEST_14083_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__0_A));
        (v_TEST_14083_n__0_INFO = SISAL_CAST(int32_t, v_LoopB_14057_n__5_MERGE_INFO));
        (v_TEST_14083_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__6_MERGE_IPVT));
        (v_TEST_14083_n__0_K = SISAL_CAST(int32_t, v_LoopB_14057_n__7_MERGE_K));
        (v_TEST_14083_n__0_LDA = SISAL_CAST(int32_t, v_LoopB_14057_n__0_LDA));
        (v_TEST_14083_n__0_LU = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__8_MERGE_LU));
        (v_TEST_14083_n__0_N = SISAL_CAST(int32_t, v_LoopB_14057_n__0_N));
        (v_TEST_14083_n__0_OLD_INFO = SISAL_CAST(int32_t, v_LoopB_14057_n__9_MERGE_OLD_INFO));
        (v_TEST_14083_n__0_OLD_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__10_MERGE_OLD_IPVT));
        (v_TEST_14083_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_14057_n__11_MERGE_OLD_K));
        (v_TEST_14083_n__0_OLD_LU = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__12_MERGE_OLD_LU));
        (v_TEST_14083_n__1_p0_o = SISAL_CAST(int32_t, 1));
        (v_TEST_14083_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_TEST_14083_n__0_N) - SISAL_CAST(int32_t, v_TEST_14083_n__1_p0_o))));
        (v_TEST_14083_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_14083_n__0_K) <= SISAL_CAST(int32_t, v_TEST_14083_n__2_p0_o))));
      }
      int32_t v_RETURNS_14082_n__0_p0_o = 0;
      sisal_array_t v_RETURNS_14082_n__0_p1_o = {0};
      sisal_array_t v_RETURNS_14082_n__0_p2_o = {0};
      (v_RETURNS_14082_n__0_p0_o = SISAL_CAST(int32_t, v_LoopB_14057_n__9_MERGE_OLD_INFO));
      (v_RETURNS_14082_n__0_p1_o = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__12_MERGE_OLD_LU));
      (v_RETURNS_14082_n__0_p2_o = SISAL_CAST(sisal_array_t, v_LoopB_14057_n__10_MERGE_OLD_IPVT));
      int32_t v_RETURNS_14082_n__1_p0_o = 0;
      (v_RETURNS_14082_n__1_p0_o = SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_RETURNS_14082_n__0_p0_o)));
      sisal_array_t v_RETURNS_14082_n__2_p0_o = {0};
      (v_RETURNS_14082_n__2_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_14082_n__0_p1_o)));
      sisal_array_t v_RETURNS_14082_n__3_p0_o = {0};
      (v_RETURNS_14082_n__3_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_14082_n__0_p2_o)));
      (v_LET_NON_REC_14056_n__1_p0_o = SISAL_CAST(int32_t, v_RETURNS_14082_n__1_p0_o));
      (v_LET_NON_REC_14056_n__1_p1_o = SISAL_CAST(sisal_array_t, v_RETURNS_14082_n__2_p0_o));
      (v_LET_NON_REC_14056_n__1_p2_o = SISAL_CAST(sisal_array_t, v_RETURNS_14082_n__3_p0_o));
    }
    sisal_array_t v_LET_NON_REC_14056_n__3_p0_o = {0};
    (v_LET_NON_REC_14056_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_i32(SISAL_CAST(sisal_array_t, v_LET_NON_REC_14056_n__1_p2_o), ((int64_t)SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__0_N)), SISAL_CAST(int32_t, SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__0_N)))));
    int32_t v_LET_NON_REC_14056_n__4_p0_o = 0;
    sisal_array_t v_IF_INTEGRAL___14085_n__0_LLU = {0};
    (v_IF_INTEGRAL___14085_n__0_LLU = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14056_n__1_p1_o));
    int32_t v_IF_INTEGRAL___14085_n__0_N = 0;
    (v_IF_INTEGRAL___14085_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__0_N));
    int32_t v_IF_INTEGRAL___14085_n__0_LINFO = 0;
    (v_IF_INTEGRAL___14085_n__0_LINFO = SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__1_p0_o));
    {
      sisal_array_t v_PREDICATE_14086_n__0_LLU = {0};
      int32_t v_PREDICATE_14086_n__0_N = 0;
      (v_PREDICATE_14086_n__0_LLU = SISAL_CAST(sisal_array_t, v_IF_INTEGRAL___14085_n__0_LLU));
      (v_PREDICATE_14086_n__0_N = SISAL_CAST(int32_t, v_IF_INTEGRAL___14085_n__0_N));
      sisal_array_t v_PREDICATE_14086_n__1_p0_o = {0};
      (v_PREDICATE_14086_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_PREDICATE_14086_n__0_LLU), (SISAL_CAST(int32_t, v_PREDICATE_14086_n__0_N) - SISAL_CAST(sisal_array_t, v_PREDICATE_14086_n__0_LLU).lower_bound[0]))));
      double v_PREDICATE_14086_n__2_p0_o = 0;
      (v_PREDICATE_14086_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_PREDICATE_14086_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_PREDICATE_14086_n__0_N) - SISAL_CAST(sisal_array_t, v_PREDICATE_14086_n__1_p0_o).lower_bound[0])]));
      double v_PREDICATE_14086_n__3_p0_o = 0;
      (v_PREDICATE_14086_n__3_p0_o = SISAL_CAST(double, 0.));
      bool v_PREDICATE_14086_n__4_p0_o = 0;
      (v_PREDICATE_14086_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_14086_n__2_p0_o) == SISAL_CAST(double, v_PREDICATE_14086_n__3_p0_o))));
      if (v_PREDICATE_14086_n__4_p0_o) {
        int32_t v_THEN_14088_n__0_N = 0;
        (v_THEN_14088_n__0_N = SISAL_CAST(int32_t, v_IF_INTEGRAL___14085_n__0_N));
        (v_LET_NON_REC_14056_n__4_p0_o = SISAL_CAST(int32_t, v_THEN_14088_n__0_N));
      }
      else {
        int32_t v_ELSE_14087_n__0_LINFO = 0;
        (v_ELSE_14087_n__0_LINFO = SISAL_CAST(int32_t, v_IF_INTEGRAL___14085_n__0_LINFO));
        (v_LET_NON_REC_14056_n__4_p0_o = SISAL_CAST(int32_t, v_ELSE_14087_n__0_LINFO));
      }
    }
    (v_g12_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14056_n__1_p1_o));
    (v_g12_n__1_p1_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_14056_n__3_p0_o));
    (v_g12_n__1_p2_o = SISAL_CAST(int32_t, v_LET_NON_REC_14056_n__4_p0_o));
  }
  (v_g12_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g12_n__1_p0_o));
  (v_g12_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g12_n__1_p1_o));
  (v_g12_n__0_p2_i = SISAL_CAST(int32_t, v_g12_n__1_p2_o));
  struct FUNC_SGEFA_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g12_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g12_n__0_p1_i));
  (__res_obj.res_2 = SISAL_CAST(int32_t, v_g12_n__0_p2_i));
  return __res_obj;
}

extern "C" struct FUNC_SGECO_results func_SGECO(sisal_array_t A, int32_t LDA, int32_t N) {
  sisal_array_t v_g13_n__0_A = {0};
  int32_t v_g13_n__0_LDA = 0;
  int32_t v_g13_n__0_N = 0;
  (v_g13_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g13_n__0_LDA = SISAL_CAST(int32_t, LDA));
  (v_g13_n__0_N = SISAL_CAST(int32_t, N));
  sisal_array_t v_g13_n__0_p0_i = {0};
  sisal_array_t v_g13_n__0_p1_i = {0};
  double v_g13_n__0_p2_i = 0;
  sisal_array_t v_g13_n__0_p3_i = {0};
  sisal_array_t v_g13_n__1_p0_o = {0};
  sisal_array_t v_g13_n__1_p1_o = {0};
  double v_g13_n__1_p2_o = 0;
  sisal_array_t v_g13_n__1_p3_o = {0};
  {
    sisal_array_t v_LET_NON_REC_13043_n__0_A = {0};
    sisal_array_t v_LET_NON_REC_13043_n__2_IVECT = {0};
    int32_t v_LET_NON_REC_13043_n__0_LDA = 0;
    sisal_array_t v_LET_NON_REC_13043_n__2_MAT = {0};
    int32_t v_LET_NON_REC_13043_n__0_N = 0;
    double v_LET_NON_REC_13043_n__2_RC = 0;
    sisal_array_t v_LET_NON_REC_13043_n__2_ZVECT = {0};
    (v_LET_NON_REC_13043_n__0_A = SISAL_CAST(sisal_array_t, v_g13_n__0_A));
    (v_LET_NON_REC_13043_n__0_LDA = SISAL_CAST(int32_t, v_g13_n__0_LDA));
    (v_LET_NON_REC_13043_n__0_N = SISAL_CAST(int32_t, v_g13_n__0_N));
    sisal_array_t v_LET_NON_REC_13043_n__1_p0_o = {0};
    sisal_array_t v_LET_NON_REC_13043_n__1_p1_o = {0};
    double v_LET_NON_REC_13043_n__1_p2_o = 0;
    sisal_array_t v_LET_NON_REC_13043_n__1_p3_o = {0};
    {
      sisal_array_t v_LET_NON_REC_13044_n__0_A = {0};
      sisal_array_t v_LET_NON_REC_13044_n__4_A1 = {0};
      double v_LET_NON_REC_13044_n__2_ANORM = 0;
      int32_t v_LET_NON_REC_13044_n__4_INFO = 0;
      sisal_array_t v_LET_NON_REC_13044_n__4_IPVT1 = {0};
      int32_t v_LET_NON_REC_13044_n__0_LDA = 0;
      int32_t v_LET_NON_REC_13044_n__0_N = 0;
      double v_LET_NON_REC_13044_n__53_RCOND = 0;
      double v_LET_NON_REC_13044_n__30_YNORM = 0;
      double v_LET_NON_REC_13044_n__47_YNORM2 = 0;
      double v_LET_NON_REC_13044_n__49_YNORM3 = 0;
      double v_LET_NON_REC_13044_n__51_YNORM4 = 0;
      sisal_array_t v_LET_NON_REC_13044_n__5_Z1 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__16_Z2 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__17_Z3 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__28_Z4 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__30_Z5 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__41_Z6 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__49_Z7 = {0};
      sisal_array_t v_LET_NON_REC_13044_n__51_Z8 = {0};
      (v_LET_NON_REC_13044_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13043_n__0_A));
      (v_LET_NON_REC_13044_n__0_LDA = SISAL_CAST(int32_t, v_LET_NON_REC_13043_n__0_LDA));
      (v_LET_NON_REC_13044_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_13043_n__0_N));
      double v_LET_NON_REC_13044_n__1_p0_o = 0;
      {
        sisal_array_t v_FORALL_13045_n__0_A = v_LET_NON_REC_13044_n__0_A;
        int32_t v_FORALL_13045_n__2_J;
        int32_t v_FORALL_13045_n__0_LDA = v_LET_NON_REC_13044_n__0_LDA;
        int32_t v_FORALL_13045_n__0_N = v_LET_NON_REC_13044_n__0_N;
        double v_FORALL_13045_n__3___forall_body_0;
        int32_t v_FORALL_13045_n__2___forall_lb_2_0;
        int32_t v_FORALL_13045_n__2___forall_ub_2_0;
        sisal_array_t v_GENERATOR_13047_n__0_A;
        int32_t v_GENERATOR_13047_n__2_J;
        int32_t v_GENERATOR_13047_n__0_LDA;
        int32_t v_GENERATOR_13047_n__0_N;
        int32_t v_GENERATOR_13047_n__2___forall_lb_2_0;
        int32_t v_GENERATOR_13047_n__2___forall_ub_2_0;
        sisal_array_t v_BODY_13048_n__0_A;
        int32_t v_BODY_13048_n__0_J;
        int32_t v_BODY_13048_n__0_LDA;
        int32_t v_BODY_13048_n__0_N;
        int32_t v_BODY_13048_n__0___forall_lb_2_0;
        int32_t v_BODY_13048_n__0___forall_ub_2_0;
        sisal_array_t v_LET_NON_REC_13049_n__0_A;
        int32_t v_LET_NON_REC_13049_n__0_J;
        int32_t v_LET_NON_REC_13049_n__0_LDA;
        int32_t v_LET_NON_REC_13049_n__0_N;
        sisal_array_t v_LET_NON_REC_13049_n__1_X;
        int32_t v_LET_NON_REC_13049_n__0___forall_lb_2_0;
        int32_t v_LET_NON_REC_13049_n__0___forall_ub_2_0;
        sisal_array_t v_LET_NON_REC_13050_n__0_A;
        int32_t v_LET_NON_REC_13050_n__0_J;
        int32_t v_LET_NON_REC_13050_n__0_LDA;
        int32_t v_LET_NON_REC_13050_n__0_N;
        sisal_array_t v_LET_NON_REC_13050_n__1_X;
        int32_t v_LET_NON_REC_13050_n__0___forall_lb_2_0;
        int32_t v_LET_NON_REC_13050_n__0___forall_ub_2_0;
        (v_GENERATOR_13047_n__0_N = v_FORALL_13045_n__0_N);
        (v_LET_NON_REC_13044_n__1_p0_o = (-1e308));
        (v_GENERATOR_13047_n__2___forall_lb_2_0 = 1);
        (v_GENERATOR_13047_n__2___forall_ub_2_0 = v_GENERATOR_13047_n__0_N);
        for ((v_GENERATOR_13047_n__2_J = 1); (v_GENERATOR_13047_n__2_J <= v_GENERATOR_13047_n__0_N); (v_GENERATOR_13047_n__2_J++)) {
          (v_BODY_13048_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_13045_n__0_A));
          (v_BODY_13048_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_13047_n__2_J));
          (v_BODY_13048_n__0_LDA = SISAL_CAST(int32_t, v_FORALL_13045_n__0_LDA));
          (v_BODY_13048_n__0_N = SISAL_CAST(int32_t, v_FORALL_13045_n__0_N));
          (v_BODY_13048_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_13047_n__2___forall_lb_2_0));
          (v_BODY_13048_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_13047_n__2___forall_ub_2_0));
          {
            (v_LET_NON_REC_13049_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_13048_n__0_A));
            (v_LET_NON_REC_13049_n__0_J = SISAL_CAST(int32_t, v_BODY_13048_n__0_J));
            (v_LET_NON_REC_13049_n__0_LDA = SISAL_CAST(int32_t, v_BODY_13048_n__0_LDA));
            (v_LET_NON_REC_13049_n__0_N = SISAL_CAST(int32_t, v_BODY_13048_n__0_N));
            (v_LET_NON_REC_13049_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_BODY_13048_n__0___forall_lb_2_0));
            (v_LET_NON_REC_13049_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_BODY_13048_n__0___forall_ub_2_0));
            (v_LET_NON_REC_13049_n__1_X = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13049_n__0_A))));
            sisal_array_t v_LET_NON_REC_13049_n__2_p0_o = {0};
            (v_LET_NON_REC_13049_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13049_n__1_X), (SISAL_CAST(int32_t, v_LET_NON_REC_13049_n__0_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_13049_n__1_X).lower_bound[0]))));
          }
          sisal_array_t v_BODY_13048_n__3_p0_o = {0};
          {
            (v_LET_NON_REC_13050_n__0_A = SISAL_CAST(sisal_array_t, v_BODY_13048_n__0_A));
            (v_LET_NON_REC_13050_n__0_J = SISAL_CAST(int32_t, v_BODY_13048_n__0_J));
            (v_LET_NON_REC_13050_n__0_LDA = SISAL_CAST(int32_t, v_BODY_13048_n__0_LDA));
            (v_LET_NON_REC_13050_n__0_N = SISAL_CAST(int32_t, v_BODY_13048_n__0_N));
            (v_LET_NON_REC_13050_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_BODY_13048_n__0___forall_lb_2_0));
            (v_LET_NON_REC_13050_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_BODY_13048_n__0___forall_ub_2_0));
            (v_LET_NON_REC_13050_n__1_X = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13050_n__0_A))));
            sisal_array_t v_LET_NON_REC_13050_n__2_p0_o = {0};
            (v_LET_NON_REC_13050_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13050_n__1_X), (SISAL_CAST(int32_t, v_LET_NON_REC_13050_n__0_J) - SISAL_CAST(sisal_array_t, v_LET_NON_REC_13050_n__1_X).lower_bound[0]))));
            (v_BODY_13048_n__3_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13050_n__2_p0_o));
          }
          double v_BODY_13048_n__5_p0_o = 0;
          (v_BODY_13048_n__5_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_BODY_13048_n__0_N), SISAL_CAST(sisal_array_t, v_BODY_13048_n__3_p0_o))));
          if ((SISAL_CAST(double, v_BODY_13048_n__5_p0_o) > v_LET_NON_REC_13044_n__1_p0_o)) {
            (v_LET_NON_REC_13044_n__1_p0_o = SISAL_CAST(double, v_BODY_13048_n__5_p0_o));
          }
        }
      }
      struct FUNC_SGEFA_results _mr_LET_NON_REC_13044_3 = func_SGEFA(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__0_A), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_LDA), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N));
      sisal_array_t v_LET_NON_REC_13044_n__3_p0_o = {0};
      (v_LET_NON_REC_13044_n__3_p0_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_13044_3.res_0));
      sisal_array_t v_LET_NON_REC_13044_n__3_p1_o = {0};
      (v_LET_NON_REC_13044_n__3_p1_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_13044_3.res_1));
      int32_t v_LET_NON_REC_13044_n__3_p2_o = 0;
      (v_LET_NON_REC_13044_n__3_p2_o = SISAL_CAST(int32_t, _mr_LET_NON_REC_13044_3.res_2));
      (v_LET_NON_REC_13044_n__5_Z1 = SISAL_CAST(sisal_array_t, func_CALC_Z1(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N))));
      int32_t v_LET_NON_REC_13044_n__6_p0_o = 0;
      (v_LET_NON_REC_13044_n__6_p0_o = SISAL_CAST(int32_t, 1));
      double v_LET_NON_REC_13044_n__7_p0_o = 0;
      (v_LET_NON_REC_13044_n__7_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__8_p0_o = 0;
      (v_LET_NON_REC_13044_n__8_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__9_p0_o = 0;
      (v_LET_NON_REC_13044_n__9_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__5_Z1))));
      float v_LET_NON_REC_13044_n__10_p0_o = 0;
      (v_LET_NON_REC_13044_n__10_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_LET_NON_REC_13044_n__8_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__9_p0_o))));
      int32_t v_LET_NON_REC_13044_n__11_p0_o = 0;
      (v_LET_NON_REC_13044_n__11_p0_o = SISAL_CAST(int32_t, 1));
      double v_LET_NON_REC_13044_n__12_p0_o = 0;
      (v_LET_NON_REC_13044_n__12_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__13_p0_o = 0;
      (v_LET_NON_REC_13044_n__13_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__14_p0_o = 0;
      (v_LET_NON_REC_13044_n__14_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__5_Z1))));
      double v_LET_NON_REC_13044_n__15_p0_o = 0;
      (v_LET_NON_REC_13044_n__15_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13044_n__13_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__14_p0_o))));
      (v_LET_NON_REC_13044_n__16_Z2 = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__11_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__5_Z1), SISAL_CAST(double, v_LET_NON_REC_13044_n__15_p0_o))));
      (v_LET_NON_REC_13044_n__17_Z3 = SISAL_CAST(sisal_array_t, func_CALC_Z3(SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__16_Z2), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p1_o), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N))));
      int32_t v_LET_NON_REC_13044_n__18_p0_o = 0;
      (v_LET_NON_REC_13044_n__18_p0_o = SISAL_CAST(int32_t, 1));
      double v_LET_NON_REC_13044_n__19_p0_o = 0;
      (v_LET_NON_REC_13044_n__19_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__20_p0_o = 0;
      (v_LET_NON_REC_13044_n__20_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__21_p0_o = 0;
      (v_LET_NON_REC_13044_n__21_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__17_Z3))));
      float v_LET_NON_REC_13044_n__22_p0_o = 0;
      (v_LET_NON_REC_13044_n__22_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_LET_NON_REC_13044_n__20_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__21_p0_o))));
      int32_t v_LET_NON_REC_13044_n__23_p0_o = 0;
      (v_LET_NON_REC_13044_n__23_p0_o = SISAL_CAST(int32_t, 1));
      double v_LET_NON_REC_13044_n__24_p0_o = 0;
      (v_LET_NON_REC_13044_n__24_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__25_p0_o = 0;
      (v_LET_NON_REC_13044_n__25_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__26_p0_o = 0;
      (v_LET_NON_REC_13044_n__26_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__17_Z3))));
      double v_LET_NON_REC_13044_n__27_p0_o = 0;
      (v_LET_NON_REC_13044_n__27_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13044_n__25_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__26_p0_o))));
      (v_LET_NON_REC_13044_n__28_Z4 = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__23_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__17_Z3), SISAL_CAST(double, v_LET_NON_REC_13044_n__27_p0_o))));
      struct FUNC_CALC_NEWZY1_results _mr_LET_NON_REC_13044_29 = func_CALC_NEWZY1(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p1_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__28_Z4));
      sisal_array_t v_LET_NON_REC_13044_n__29_p0_o = {0};
      (v_LET_NON_REC_13044_n__29_p0_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_13044_29.res_0));
      double v_LET_NON_REC_13044_n__29_p1_o = 0;
      (v_LET_NON_REC_13044_n__29_p1_o = SISAL_CAST(double, _mr_LET_NON_REC_13044_29.res_1));
      int32_t v_LET_NON_REC_13044_n__31_p0_o = 0;
      (v_LET_NON_REC_13044_n__31_p0_o = SISAL_CAST(int32_t, 1));
      double v_LET_NON_REC_13044_n__32_p0_o = 0;
      (v_LET_NON_REC_13044_n__32_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__33_p0_o = 0;
      (v_LET_NON_REC_13044_n__33_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__34_p0_o = 0;
      (v_LET_NON_REC_13044_n__34_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__29_p0_o))));
      float v_LET_NON_REC_13044_n__35_p0_o = 0;
      (v_LET_NON_REC_13044_n__35_p0_o = SISAL_CAST(float, (SISAL_CAST(double, v_LET_NON_REC_13044_n__33_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__34_p0_o))));
      int32_t v_LET_NON_REC_13044_n__36_p0_o = 0;
      (v_LET_NON_REC_13044_n__36_p0_o = SISAL_CAST(int32_t, 1));
      double v_LET_NON_REC_13044_n__37_p0_o = 0;
      (v_LET_NON_REC_13044_n__37_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__38_p0_o = 0;
      (v_LET_NON_REC_13044_n__38_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__39_p0_o = 0;
      (v_LET_NON_REC_13044_n__39_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__29_p0_o))));
      double v_LET_NON_REC_13044_n__40_p0_o = 0;
      (v_LET_NON_REC_13044_n__40_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13044_n__38_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__39_p0_o))));
      (v_LET_NON_REC_13044_n__41_Z6 = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__36_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__29_p0_o), SISAL_CAST(double, v_LET_NON_REC_13044_n__40_p0_o))));
      double v_LET_NON_REC_13044_n__42_p0_o = 0;
      (v_LET_NON_REC_13044_n__42_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__43_p0_o = 0;
      (v_LET_NON_REC_13044_n__43_p0_o = SISAL_CAST(double, 1.));
      double v_LET_NON_REC_13044_n__44_p0_o = 0;
      (v_LET_NON_REC_13044_n__44_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__29_p0_o))));
      double v_LET_NON_REC_13044_n__45_p0_o = 0;
      (v_LET_NON_REC_13044_n__45_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13044_n__43_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13044_n__44_p0_o))));
      (v_LET_NON_REC_13044_n__47_YNORM2 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13044_n__45_p0_o) * SISAL_CAST(double, v_LET_NON_REC_13044_n__29_p1_o))));
      struct FUNC_CALC_NEWZY2_results _mr_LET_NON_REC_13044_48 = func_CALC_NEWZY2(SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p0_o), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__41_Z6), SISAL_CAST(double, v_LET_NON_REC_13044_n__47_YNORM2));
      sisal_array_t v_LET_NON_REC_13044_n__48_p0_o = {0};
      (v_LET_NON_REC_13044_n__48_p0_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_13044_48.res_0));
      double v_LET_NON_REC_13044_n__48_p1_o = 0;
      (v_LET_NON_REC_13044_n__48_p1_o = SISAL_CAST(double, _mr_LET_NON_REC_13044_48.res_1));
      sisal_array_t v_LET_NON_REC_13044_n__50_p0_o = {0};
      double v_LET_NON_REC_13044_n__50_p1_o = 0;
      {
        sisal_array_t v_LET_NON_REC_13051_n__0_A = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_A1 = {0};
        double v_LET_NON_REC_13051_n__0_ANORM = 0;
        int32_t v_LET_NON_REC_13051_n__0_INFO = 0;
        sisal_array_t v_LET_NON_REC_13051_n__0_IPVT1 = {0};
        int32_t v_LET_NON_REC_13051_n__0_LDA = 0;
        int32_t v_LET_NON_REC_13051_n__0_N = 0;
        double v_LET_NON_REC_13051_n__4_S3 = 0;
        double v_LET_NON_REC_13051_n__0_YNORM = 0;
        double v_LET_NON_REC_13051_n__0_YNORM2 = 0;
        double v_LET_NON_REC_13051_n__0_YNORM3 = 0;
        sisal_array_t v_LET_NON_REC_13051_n__0_Z1 = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_Z2 = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_Z3 = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_Z4 = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_Z5 = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_Z6 = {0};
        sisal_array_t v_LET_NON_REC_13051_n__0_Z7 = {0};
        (v_LET_NON_REC_13051_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__0_A));
        (v_LET_NON_REC_13051_n__0_A1 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p0_o));
        (v_LET_NON_REC_13051_n__0_ANORM = SISAL_CAST(double, v_LET_NON_REC_13044_n__1_p0_o));
        (v_LET_NON_REC_13051_n__0_INFO = SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__3_p2_o));
        (v_LET_NON_REC_13051_n__0_IPVT1 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p1_o));
        (v_LET_NON_REC_13051_n__0_LDA = SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_LDA));
        (v_LET_NON_REC_13051_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_13044_n__0_N));
        (v_LET_NON_REC_13051_n__0_YNORM = SISAL_CAST(double, v_LET_NON_REC_13044_n__29_p1_o));
        (v_LET_NON_REC_13051_n__0_YNORM2 = SISAL_CAST(double, v_LET_NON_REC_13044_n__47_YNORM2));
        (v_LET_NON_REC_13051_n__0_YNORM3 = SISAL_CAST(double, v_LET_NON_REC_13044_n__48_p1_o));
        (v_LET_NON_REC_13051_n__0_Z1 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__5_Z1));
        (v_LET_NON_REC_13051_n__0_Z2 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__16_Z2));
        (v_LET_NON_REC_13051_n__0_Z3 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__17_Z3));
        (v_LET_NON_REC_13051_n__0_Z4 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__28_Z4));
        (v_LET_NON_REC_13051_n__0_Z5 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__29_p0_o));
        (v_LET_NON_REC_13051_n__0_Z6 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__41_Z6));
        (v_LET_NON_REC_13051_n__0_Z7 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__48_p0_o));
        double v_LET_NON_REC_13051_n__1_p0_o = 0;
        (v_LET_NON_REC_13051_n__1_p0_o = SISAL_CAST(double, 1.));
        double v_LET_NON_REC_13051_n__2_p0_o = 0;
        (v_LET_NON_REC_13051_n__2_p0_o = SISAL_CAST(double, 1.));
        double v_LET_NON_REC_13051_n__3_p0_o = 0;
        (v_LET_NON_REC_13051_n__3_p0_o = SISAL_CAST(double, func_SASUM(SISAL_CAST(int32_t, v_LET_NON_REC_13051_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13051_n__0_Z7))));
        (v_LET_NON_REC_13051_n__4_S3 = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13051_n__2_p0_o) / SISAL_CAST(double, v_LET_NON_REC_13051_n__3_p0_o))));
        int32_t v_LET_NON_REC_13051_n__5_p0_o = 0;
        (v_LET_NON_REC_13051_n__5_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_LET_NON_REC_13051_n__6_p0_o = 0;
        (v_LET_NON_REC_13051_n__6_p0_o = SISAL_CAST(int32_t, 1));
        sisal_array_t v_LET_NON_REC_13051_n__7_p0_o = {0};
        (v_LET_NON_REC_13051_n__7_p0_o = SISAL_CAST(sisal_array_t, func_SSCAL(SISAL_CAST(int32_t, v_LET_NON_REC_13051_n__6_p0_o), SISAL_CAST(int32_t, v_LET_NON_REC_13051_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_13051_n__0_Z7), SISAL_CAST(double, v_LET_NON_REC_13051_n__4_S3))));
        double v_LET_NON_REC_13051_n__8_p0_o = 0;
        (v_LET_NON_REC_13051_n__8_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_LET_NON_REC_13051_n__0_YNORM3) * SISAL_CAST(double, v_LET_NON_REC_13051_n__4_S3))));
        (v_LET_NON_REC_13044_n__50_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13051_n__7_p0_o));
        (v_LET_NON_REC_13044_n__50_p1_o = SISAL_CAST(double, v_LET_NON_REC_13051_n__8_p0_o));
      }
      double v_LET_NON_REC_13044_n__52_p0_o = 0;
      double v_IF_DOUBLE___13052_n__0_ANORM = 0;
      (v_IF_DOUBLE___13052_n__0_ANORM = SISAL_CAST(double, v_LET_NON_REC_13044_n__1_p0_o));
      double v_IF_DOUBLE___13052_n__0_YNORM4 = 0;
      (v_IF_DOUBLE___13052_n__0_YNORM4 = SISAL_CAST(double, v_LET_NON_REC_13044_n__50_p1_o));
      {
        double v_PREDICATE_13053_n__0_ANORM = 0;
        (v_PREDICATE_13053_n__0_ANORM = SISAL_CAST(double, v_IF_DOUBLE___13052_n__0_ANORM));
        double v_PREDICATE_13053_n__1_p0_o = 0;
        (v_PREDICATE_13053_n__1_p0_o = SISAL_CAST(double, 0.));
        bool v_PREDICATE_13053_n__2_p0_o = 0;
        (v_PREDICATE_13053_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_13053_n__0_ANORM) == SISAL_CAST(double, v_PREDICATE_13053_n__1_p0_o))));
        if (v_PREDICATE_13053_n__2_p0_o) {
          double v_THEN_13055_n__1_p0_o = 0;
          (v_THEN_13055_n__1_p0_o = SISAL_CAST(double, 0.));
          (v_LET_NON_REC_13044_n__52_p0_o = SISAL_CAST(double, v_THEN_13055_n__1_p0_o));
        }
        else {
          double v_ELSE_13054_n__0_ANORM = 0;
          double v_ELSE_13054_n__0_YNORM4 = 0;
          (v_ELSE_13054_n__0_YNORM4 = SISAL_CAST(double, v_IF_DOUBLE___13052_n__0_YNORM4));
          (v_ELSE_13054_n__0_ANORM = SISAL_CAST(double, v_IF_DOUBLE___13052_n__0_ANORM));
          double v_ELSE_13054_n__1_p0_o = 0;
          (v_ELSE_13054_n__1_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_ELSE_13054_n__0_YNORM4) / SISAL_CAST(double, v_ELSE_13054_n__0_ANORM))));
          (v_LET_NON_REC_13044_n__52_p0_o = SISAL_CAST(double, v_ELSE_13054_n__1_p0_o));
        }
      }
      (v_LET_NON_REC_13043_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p0_o));
      (v_LET_NON_REC_13043_n__1_p1_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__3_p1_o));
      (v_LET_NON_REC_13043_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_13044_n__52_p0_o));
      (v_LET_NON_REC_13043_n__1_p3_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13044_n__50_p0_o));
    }
    (v_g13_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13043_n__1_p0_o));
    (v_g13_n__1_p1_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13043_n__1_p1_o));
    (v_g13_n__1_p2_o = SISAL_CAST(double, v_LET_NON_REC_13043_n__1_p2_o));
    (v_g13_n__1_p3_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_13043_n__1_p3_o));
  }
  (v_g13_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g13_n__1_p0_o));
  (v_g13_n__0_p1_i = SISAL_CAST(sisal_array_t, v_g13_n__1_p1_o));
  (v_g13_n__0_p2_i = SISAL_CAST(double, v_g13_n__1_p2_o));
  (v_g13_n__0_p3_i = SISAL_CAST(sisal_array_t, v_g13_n__1_p3_o));
  struct FUNC_SGECO_results __res_obj;
  (__res_obj.res_0 = SISAL_CAST(sisal_array_t, v_g13_n__0_p0_i));
  (__res_obj.res_1 = SISAL_CAST(sisal_array_t, v_g13_n__0_p1_i));
  (__res_obj.res_2 = SISAL_CAST(double, v_g13_n__0_p2_i));
  (__res_obj.res_3 = SISAL_CAST(sisal_array_t, v_g13_n__0_p3_i));
  return __res_obj;
}

extern "C" sisal_array_t func_SGESL(sisal_array_t A, int32_t N, sisal_array_t IPVT, sisal_array_t B) {
  sisal_array_t v_g14_n__0_A = {0};
  sisal_array_t v_g14_n__0_B = {0};
  sisal_array_t v_g14_n__0_IPVT = {0};
  int32_t v_g14_n__0_N = 0;
  (v_g14_n__0_A = SISAL_CAST(sisal_array_t, A));
  (v_g14_n__0_N = SISAL_CAST(int32_t, N));
  (v_g14_n__0_IPVT = SISAL_CAST(sisal_array_t, IPVT));
  (v_g14_n__0_B = SISAL_CAST(sisal_array_t, B));
  sisal_array_t v_g14_n__0_p0_i = {0};
  sisal_array_t v_g14_n__1_p0_o = {0};
  {
    sisal_array_t v_LET_NON_REC_12020_n__0_A = {0};
    sisal_array_t v_LET_NON_REC_12020_n__0_B = {0};
    sisal_array_t v_LET_NON_REC_12020_n__2_BKS = {0};
    sisal_array_t v_LET_NON_REC_12020_n__0_IPVT = {0};
    int32_t v_LET_NON_REC_12020_n__0_N = 0;
    (v_LET_NON_REC_12020_n__0_A = SISAL_CAST(sisal_array_t, v_g14_n__0_A));
    (v_LET_NON_REC_12020_n__0_B = SISAL_CAST(sisal_array_t, v_g14_n__0_B));
    (v_LET_NON_REC_12020_n__0_IPVT = SISAL_CAST(sisal_array_t, v_g14_n__0_IPVT));
    (v_LET_NON_REC_12020_n__0_N = SISAL_CAST(int32_t, v_g14_n__0_N));
    sisal_array_t v_LET_NON_REC_12020_n__1_p0_o = {0};
    int32_t v_IF_array_dv_DOUBLE____12021_n__0_N = 0;
    (v_IF_array_dv_DOUBLE____12021_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_12020_n__0_N));
    sisal_array_t v_IF_array_dv_DOUBLE____12021_n__0_B = {0};
    (v_IF_array_dv_DOUBLE____12021_n__0_B = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__0_B));
    sisal_array_t v_IF_array_dv_DOUBLE____12021_n__0_A = {0};
    (v_IF_array_dv_DOUBLE____12021_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__0_A));
    sisal_array_t v_IF_array_dv_DOUBLE____12021_n__0_IPVT = {0};
    (v_IF_array_dv_DOUBLE____12021_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__0_IPVT));
    {
      int32_t v_PREDICATE_12022_n__0_N = 0;
      (v_PREDICATE_12022_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____12021_n__0_N));
      int32_t v_PREDICATE_12022_n__1_p0_o = 0;
      (v_PREDICATE_12022_n__1_p0_o = SISAL_CAST(int32_t, 1));
      int32_t v_PREDICATE_12022_n__2_p0_o = 0;
      (v_PREDICATE_12022_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_PREDICATE_12022_n__0_N) - SISAL_CAST(int32_t, v_PREDICATE_12022_n__1_p0_o))));
      int32_t v_PREDICATE_12022_n__3_p0_o = 0;
      (v_PREDICATE_12022_n__3_p0_o = SISAL_CAST(int32_t, 1));
      bool v_PREDICATE_12022_n__4_p0_o = 0;
      (v_PREDICATE_12022_n__4_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_12022_n__2_p0_o) >= SISAL_CAST(int32_t, v_PREDICATE_12022_n__3_p0_o))));
      if (v_PREDICATE_12022_n__4_p0_o) {
        sisal_array_t v_THEN_12024_n__0_A = {0};
        sisal_array_t v_THEN_12024_n__0_B = {0};
        sisal_array_t v_THEN_12024_n__0_IPVT = {0};
        int32_t v_THEN_12024_n__0_N = 0;
        (v_THEN_12024_n__0_A = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____12021_n__0_A));
        (v_THEN_12024_n__0_B = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____12021_n__0_B));
        (v_THEN_12024_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____12021_n__0_IPVT));
        (v_THEN_12024_n__0_N = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____12021_n__0_N));
        sisal_array_t v_THEN_12024_n__1_p0_o = {0};
        {
          int32_t v_LoopB_12025_n__5_MERGE_K = 0;
          sisal_array_t v_LoopB_12025_n__6_MERGE_NEWB = {0};
          int32_t v_LoopB_12025_n__7_MERGE_OLD_K = 0;
          sisal_array_t v_LoopB_12025_n__8_MERGE_OLD_NEWB = {0};
          bool v_LoopB_12025_n__9_MERGE_first = 0;
          sisal_array_t v_LoopB_12025_bodycap_n14_p0 = {0};
          int32_t v_LoopB_12025_bodycap_n16_p0 = 0;
          bool v_LoopB_12025_bodycap_n17_p0 = 0;
          sisal_array_t v_LoopB_12025_n__0_A = {0};
          (v_LoopB_12025_n__0_A = SISAL_CAST(sisal_array_t, v_THEN_12024_n__0_A));
          sisal_array_t v_LoopB_12025_n__0_B = {0};
          (v_LoopB_12025_n__0_B = SISAL_CAST(sisal_array_t, v_THEN_12024_n__0_B));
          sisal_array_t v_LoopB_12025_n__0_IPVT = {0};
          (v_LoopB_12025_n__0_IPVT = SISAL_CAST(sisal_array_t, v_THEN_12024_n__0_IPVT));
          int32_t v_LoopB_12025_n__0_N = 0;
          (v_LoopB_12025_n__0_N = SISAL_CAST(int32_t, v_THEN_12024_n__0_N));
          sisal_array_t v_INIT_12033_n__0_A = {0};
          sisal_array_t v_INIT_12033_n__0_B = {0};
          sisal_array_t v_INIT_12033_n__0_IPVT = {0};
          int32_t v_INIT_12033_n__1_K = 0;
          int32_t v_INIT_12033_n__0_N = 0;
          sisal_array_t v_INIT_12033_n__0_NEWB = {0};
          int32_t v_INIT_12033_n__1_OLD_K = 0;
          sisal_array_t v_INIT_12033_n__0_OLD_NEWB = {0};
          (v_INIT_12033_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_A));
          (v_INIT_12033_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_B));
          (v_INIT_12033_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_IPVT));
          (v_INIT_12033_n__0_N = SISAL_CAST(int32_t, v_LoopB_12025_n__0_N));
          (v_INIT_12033_n__1_OLD_K = SISAL_CAST(int32_t, 1));
          bool v_INIT_12033_n__2_p0_o = 0;
          (v_INIT_12033_n__2_p0_o = SISAL_CAST(bool, true));
          (v_LoopB_12025_n__5_MERGE_K = v_INIT_12033_n__1_OLD_K);
          (v_LoopB_12025_n__6_MERGE_NEWB = v_INIT_12033_n__0_OLD_NEWB);
          (v_LoopB_12025_n__7_MERGE_OLD_K = v_INIT_12033_n__1_OLD_K);
          (v_LoopB_12025_n__8_MERGE_OLD_NEWB = v_INIT_12033_n__0_OLD_NEWB);
          (v_LoopB_12025_n__9_MERGE_first = v_INIT_12033_n__2_p0_o);
          sisal_array_t v_TEST_12032_n__0_A = {0};
          sisal_array_t v_TEST_12032_n__0_B = {0};
          sisal_array_t v_TEST_12032_n__0_IPVT = {0};
          int32_t v_TEST_12032_n__0_K = 0;
          int32_t v_TEST_12032_n__0_N = 0;
          sisal_array_t v_TEST_12032_n__0_NEWB = {0};
          int32_t v_TEST_12032_n__0_OLD_K = 0;
          sisal_array_t v_TEST_12032_n__0_OLD_NEWB = {0};
          (v_TEST_12032_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_A));
          (v_TEST_12032_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_B));
          (v_TEST_12032_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_IPVT));
          (v_TEST_12032_n__0_K = SISAL_CAST(int32_t, v_LoopB_12025_n__5_MERGE_K));
          (v_TEST_12032_n__0_N = SISAL_CAST(int32_t, v_LoopB_12025_n__0_N));
          (v_TEST_12032_n__0_NEWB = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__6_MERGE_NEWB));
          (v_TEST_12032_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_12025_n__7_MERGE_OLD_K));
          (v_TEST_12032_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__8_MERGE_OLD_NEWB));
          int32_t v_TEST_12032_n__1_p0_o = 0;
          (v_TEST_12032_n__1_p0_o = SISAL_CAST(int32_t, 1));
          int32_t v_TEST_12032_n__2_p0_o = 0;
          (v_TEST_12032_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_TEST_12032_n__0_N) - SISAL_CAST(int32_t, v_TEST_12032_n__1_p0_o))));
          bool v_TEST_12032_n__3_p0_o = 0;
          (v_TEST_12032_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_12032_n__0_K) <= SISAL_CAST(int32_t, v_TEST_12032_n__2_p0_o))));
          #ifdef SISAL_TRAP_ZERO_TRIP
          if ((!v_TEST_12032_n__3_p0_o)) {
            fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_12025 executed 0 times (guard false on entry)\n");
            exit(1);
          }
          #endif
          while (v_TEST_12032_n__3_p0_o) {
            sisal_array_t v_BODY_12026_n__0_A = {0};
            sisal_array_t v_BODY_12026_n__0_B = {0};
            sisal_array_t v_BODY_12026_n__0_IPVT = {0};
            int32_t v_BODY_12026_n__16_K = 0;
            int32_t v_BODY_12026_n__1_L = 0;
            int32_t v_BODY_12026_n__0_N = 0;
            sisal_array_t v_BODY_12026_n__14_NEWB = {0};
            int32_t v_BODY_12026_n__0_OLD_K = 0;
            sisal_array_t v_BODY_12026_n__0_OLD_NEWB = {0};
            double v_BODY_12026_n__2_T = 0;
            sisal_array_t v_BODY_12026_n__3_TEMPB = {0};
            sisal_array_t v_BODY_12026_n__5_TRANS_A = {0};
            (v_BODY_12026_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_A));
            (v_BODY_12026_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_B));
            (v_BODY_12026_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_IPVT));
            int32_t v_BODY_12026_n__0_p3_o = 0;
            (v_BODY_12026_n__0_p3_o = SISAL_CAST(int32_t, v_LoopB_12025_n__5_MERGE_K));
            (v_BODY_12026_n__0_N = SISAL_CAST(int32_t, v_LoopB_12025_n__0_N));
            sisal_array_t v_BODY_12026_n__0_p5_o = {0};
            (v_BODY_12026_n__0_p5_o = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__6_MERGE_NEWB));
            (v_BODY_12026_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_12025_n__7_MERGE_OLD_K));
            (v_BODY_12026_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__8_MERGE_OLD_NEWB));
            (v_BODY_12026_n__1_L = SISAL_CAST(int32_t, ((int32_t *)SISAL_CAST(sisal_array_t, v_BODY_12026_n__0_IPVT).data)[(SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_12026_n__0_IPVT).lower_bound[0])]));
            (v_BODY_12026_n__2_T = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_12026_n__0_OLD_NEWB).data)[(SISAL_CAST(int32_t, v_BODY_12026_n__1_L) - SISAL_CAST(sisal_array_t, v_BODY_12026_n__0_OLD_NEWB).lower_bound[0])]));
            int32_t v_IF_array_dv_DOUBLE____12027_n__0_L = 0;
            (v_IF_array_dv_DOUBLE____12027_n__0_L = SISAL_CAST(int32_t, v_BODY_12026_n__1_L));
            int32_t v_IF_array_dv_DOUBLE____12027_n__0_OLD_K = 0;
            (v_IF_array_dv_DOUBLE____12027_n__0_OLD_K = SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K));
            sisal_array_t v_IF_array_dv_DOUBLE____12027_n__0_OLD_NEWB = {0};
            (v_IF_array_dv_DOUBLE____12027_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_BODY_12026_n__0_OLD_NEWB));
            double v_IF_array_dv_DOUBLE____12027_n__0_T = 0;
            (v_IF_array_dv_DOUBLE____12027_n__0_T = SISAL_CAST(double, v_BODY_12026_n__2_T));
            {
              int32_t v_PREDICATE_12028_n__0_L = 0;
              int32_t v_PREDICATE_12028_n__0_OLD_K = 0;
              (v_PREDICATE_12028_n__0_L = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____12027_n__0_L));
              (v_PREDICATE_12028_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____12027_n__0_OLD_K));
              bool v_PREDICATE_12028_n__1_p0_o = 0;
              (v_PREDICATE_12028_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_PREDICATE_12028_n__0_L) != SISAL_CAST(int32_t, v_PREDICATE_12028_n__0_OLD_K))));
              if (v_PREDICATE_12028_n__1_p0_o) {
                int32_t v_THEN_12030_n__0_L = 0;
                int32_t v_THEN_12030_n__0_OLD_K = 0;
                sisal_array_t v_THEN_12030_n__0_OLD_NEWB = {0};
                double v_THEN_12030_n__0_T = 0;
                (v_THEN_12030_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____12027_n__0_OLD_NEWB));
                (v_THEN_12030_n__0_OLD_K = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____12027_n__0_OLD_K));
                (v_THEN_12030_n__0_L = SISAL_CAST(int32_t, v_IF_array_dv_DOUBLE____12027_n__0_L));
                (v_THEN_12030_n__0_T = SISAL_CAST(double, v_IF_array_dv_DOUBLE____12027_n__0_T));
                double v_THEN_12030_n__1_p0_o = 0;
                (v_THEN_12030_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_THEN_12030_n__0_OLD_NEWB).data)[(SISAL_CAST(int32_t, v_THEN_12030_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_THEN_12030_n__0_OLD_NEWB).lower_bound[0])]));
                sisal_array_t v_THEN_12030_n__2_p0_o = {0};
                (v_THEN_12030_n__2_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_12030_n__0_OLD_NEWB), ((int64_t)SISAL_CAST(int32_t, v_THEN_12030_n__0_L)), SISAL_CAST(double, SISAL_CAST(double, v_THEN_12030_n__1_p0_o)))));
                sisal_array_t v_THEN_12030_n__3_p0_o = {0};
                (v_THEN_12030_n__3_p0_o = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_THEN_12030_n__2_p0_o), ((int64_t)SISAL_CAST(int32_t, v_THEN_12030_n__0_OLD_K)), SISAL_CAST(double, SISAL_CAST(double, v_THEN_12030_n__0_T)))));
                (v_BODY_12026_n__3_TEMPB = SISAL_CAST(sisal_array_t, v_THEN_12030_n__3_p0_o));
              }
              else {
                sisal_array_t v_ELSE_12029_n__0_OLD_NEWB = {0};
                (v_ELSE_12029_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____12027_n__0_OLD_NEWB));
                (v_BODY_12026_n__3_TEMPB = SISAL_CAST(sisal_array_t, v_ELSE_12029_n__0_OLD_NEWB));
              }
            }
            (v_BODY_12026_n__5_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_BODY_12026_n__0_A))));
            int32_t v_BODY_12026_n__6_p0_o = 0;
            (v_BODY_12026_n__6_p0_o = SISAL_CAST(int32_t, 1));
            float v_BODY_12026_n__7_p0_o = 0;
            (v_BODY_12026_n__7_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K) + SISAL_CAST(int32_t, v_BODY_12026_n__6_p0_o))));
            float v_BODY_12026_n__8_p0_o = 0;
            (v_BODY_12026_n__8_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_BODY_12026_n__0_N) - SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K))));
            float v_BODY_12026_n__9_p0_o = 0;
            (v_BODY_12026_n__9_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_12026_n__5_TRANS_A).data)[(SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_12026_n__5_TRANS_A).lower_bound[0])]));
            int32_t v_BODY_12026_n__10_p0_o = 0;
            (v_BODY_12026_n__10_p0_o = SISAL_CAST(int32_t, 1));
            int32_t v_BODY_12026_n__11_p0_o = 0;
            (v_BODY_12026_n__11_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K) + SISAL_CAST(int32_t, v_BODY_12026_n__10_p0_o))));
            int32_t v_BODY_12026_n__12_p0_o = 0;
            (v_BODY_12026_n__12_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12026_n__0_N) - SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K))));
            sisal_array_t v_BODY_12026_n__13_p0_o = {0};
            (v_BODY_12026_n__13_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_12026_n__5_TRANS_A), (SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K) - SISAL_CAST(sisal_array_t, v_BODY_12026_n__5_TRANS_A).lower_bound[0]))));
            (v_BODY_12026_n__14_NEWB = SISAL_CAST(sisal_array_t, func_SAXPY(SISAL_CAST(int32_t, v_BODY_12026_n__11_p0_o), SISAL_CAST(int32_t, v_BODY_12026_n__12_p0_o), SISAL_CAST(double, v_BODY_12026_n__2_T), SISAL_CAST(sisal_array_t, v_BODY_12026_n__13_p0_o), SISAL_CAST(sisal_array_t, v_BODY_12026_n__3_TEMPB))));
            int32_t v_BODY_12026_n__15_p0_o = 0;
            (v_BODY_12026_n__15_p0_o = SISAL_CAST(int32_t, 1));
            (v_BODY_12026_n__16_K = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12026_n__0_OLD_K) + SISAL_CAST(int32_t, v_BODY_12026_n__15_p0_o))));
            bool v_BODY_12026_n__17_p0_o = 0;
            (v_BODY_12026_n__17_p0_o = SISAL_CAST(bool, false));
            (v_LoopB_12025_bodycap_n14_p0 = v_BODY_12026_n__14_NEWB);
            (v_LoopB_12025_bodycap_n16_p0 = v_BODY_12026_n__16_K);
            (v_LoopB_12025_bodycap_n17_p0 = v_BODY_12026_n__17_p0_o);
            (v_LoopB_12025_n__5_MERGE_K = v_LoopB_12025_bodycap_n16_p0);
            (v_LoopB_12025_n__6_MERGE_NEWB = v_LoopB_12025_bodycap_n14_p0);
            (v_LoopB_12025_n__7_MERGE_OLD_K = v_LoopB_12025_bodycap_n16_p0);
            (v_LoopB_12025_n__8_MERGE_OLD_NEWB = v_LoopB_12025_bodycap_n14_p0);
            (v_LoopB_12025_n__9_MERGE_first = v_LoopB_12025_bodycap_n17_p0);
            (v_TEST_12032_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_A));
            (v_TEST_12032_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_B));
            (v_TEST_12032_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__0_IPVT));
            (v_TEST_12032_n__0_K = SISAL_CAST(int32_t, v_LoopB_12025_n__5_MERGE_K));
            (v_TEST_12032_n__0_N = SISAL_CAST(int32_t, v_LoopB_12025_n__0_N));
            (v_TEST_12032_n__0_NEWB = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__6_MERGE_NEWB));
            (v_TEST_12032_n__0_OLD_K = SISAL_CAST(int32_t, v_LoopB_12025_n__7_MERGE_OLD_K));
            (v_TEST_12032_n__0_OLD_NEWB = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__8_MERGE_OLD_NEWB));
            (v_TEST_12032_n__1_p0_o = SISAL_CAST(int32_t, 1));
            (v_TEST_12032_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_TEST_12032_n__0_N) - SISAL_CAST(int32_t, v_TEST_12032_n__1_p0_o))));
            (v_TEST_12032_n__3_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_12032_n__0_K) <= SISAL_CAST(int32_t, v_TEST_12032_n__2_p0_o))));
          }
          sisal_array_t v_RETURNS_12031_n__0_p0_o = {0};
          (v_RETURNS_12031_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_12025_n__8_MERGE_OLD_NEWB));
          sisal_array_t v_RETURNS_12031_n__1_p0_o = {0};
          (v_RETURNS_12031_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_12031_n__0_p0_o)));
          (v_THEN_12024_n__1_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_12031_n__1_p0_o));
        }
        (v_LET_NON_REC_12020_n__1_p0_o = SISAL_CAST(sisal_array_t, v_THEN_12024_n__1_p0_o));
      }
      else {
        sisal_array_t v_ELSE_12023_n__0_B = {0};
        (v_ELSE_12023_n__0_B = SISAL_CAST(sisal_array_t, v_IF_array_dv_DOUBLE____12021_n__0_B));
        (v_LET_NON_REC_12020_n__1_p0_o = SISAL_CAST(sisal_array_t, v_ELSE_12023_n__0_B));
      }
    }
    sisal_array_t v_LET_NON_REC_12020_n__3_p0_o = {0};
    {
      sisal_array_t v_LoopB_12034_n__5_MERGE_BOTHER = {0};
      int32_t v_LoopB_12034_n__6_MERGE_K2 = 0;
      sisal_array_t v_LoopB_12034_n__7_MERGE_OLD_BOTHER = {0};
      int32_t v_LoopB_12034_n__8_MERGE_OLD_K2 = 0;
      bool v_LoopB_12034_n__9_MERGE_first = 0;
      int32_t v_LoopB_12034_bodycap_n25_p0 = 0;
      sisal_array_t v_LoopB_12034_bodycap_n26_p0 = {0};
      bool v_LoopB_12034_bodycap_n27_p0 = 0;
      sisal_array_t v_LoopB_12034_n__0_A = {0};
      (v_LoopB_12034_n__0_A = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__0_A));
      sisal_array_t v_LoopB_12034_n__0_B = {0};
      (v_LoopB_12034_n__0_B = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__0_B));
      sisal_array_t v_LoopB_12034_n__0_BKS = {0};
      (v_LoopB_12034_n__0_BKS = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__1_p0_o));
      sisal_array_t v_LoopB_12034_n__0_IPVT = {0};
      (v_LoopB_12034_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__0_IPVT));
      int32_t v_LoopB_12034_n__0_N = 0;
      (v_LoopB_12034_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_12020_n__0_N));
      sisal_array_t v_INIT_12042_n__0_A = {0};
      sisal_array_t v_INIT_12042_n__0_B = {0};
      sisal_array_t v_INIT_12042_n__0_BKS = {0};
      sisal_array_t v_INIT_12042_n__0_BOTHER = {0};
      sisal_array_t v_INIT_12042_n__0_IPVT = {0};
      int32_t v_INIT_12042_n__1_K2 = 0;
      int32_t v_INIT_12042_n__0_N = 0;
      sisal_array_t v_INIT_12042_n__0_OLD_BOTHER = {0};
      int32_t v_INIT_12042_n__1_OLD_K2 = 0;
      (v_INIT_12042_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_A));
      (v_INIT_12042_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_B));
      (v_INIT_12042_n__0_OLD_BOTHER = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_BKS));
      (v_INIT_12042_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_IPVT));
      (v_INIT_12042_n__0_N = SISAL_CAST(int32_t, v_LoopB_12034_n__0_N));
      (v_INIT_12042_n__1_OLD_K2 = SISAL_CAST(int32_t, 1));
      bool v_INIT_12042_n__2_p0_o = 0;
      (v_INIT_12042_n__2_p0_o = SISAL_CAST(bool, true));
      (v_LoopB_12034_n__5_MERGE_BOTHER = v_INIT_12042_n__0_OLD_BOTHER);
      (v_LoopB_12034_n__6_MERGE_K2 = v_INIT_12042_n__1_OLD_K2);
      (v_LoopB_12034_n__7_MERGE_OLD_BOTHER = v_INIT_12042_n__0_OLD_BOTHER);
      (v_LoopB_12034_n__8_MERGE_OLD_K2 = v_INIT_12042_n__1_OLD_K2);
      (v_LoopB_12034_n__9_MERGE_first = v_INIT_12042_n__2_p0_o);
      sisal_array_t v_TEST_12041_n__0_A = {0};
      sisal_array_t v_TEST_12041_n__0_B = {0};
      sisal_array_t v_TEST_12041_n__0_BKS = {0};
      sisal_array_t v_TEST_12041_n__0_BOTHER = {0};
      sisal_array_t v_TEST_12041_n__0_IPVT = {0};
      int32_t v_TEST_12041_n__0_K2 = 0;
      int32_t v_TEST_12041_n__0_N = 0;
      sisal_array_t v_TEST_12041_n__0_OLD_BOTHER = {0};
      int32_t v_TEST_12041_n__0_OLD_K2 = 0;
      (v_TEST_12041_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_A));
      (v_TEST_12041_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_B));
      (v_TEST_12041_n__0_BKS = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_BKS));
      (v_TEST_12041_n__0_BOTHER = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__5_MERGE_BOTHER));
      (v_TEST_12041_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_IPVT));
      (v_TEST_12041_n__0_K2 = SISAL_CAST(int32_t, v_LoopB_12034_n__6_MERGE_K2));
      (v_TEST_12041_n__0_N = SISAL_CAST(int32_t, v_LoopB_12034_n__0_N));
      (v_TEST_12041_n__0_OLD_BOTHER = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__7_MERGE_OLD_BOTHER));
      (v_TEST_12041_n__0_OLD_K2 = SISAL_CAST(int32_t, v_LoopB_12034_n__8_MERGE_OLD_K2));
      bool v_TEST_12041_n__1_p0_o = 0;
      (v_TEST_12041_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_12041_n__0_K2) <= SISAL_CAST(int32_t, v_TEST_12041_n__0_N))));
      #ifdef SISAL_TRAP_ZERO_TRIP
      if ((!v_TEST_12041_n__1_p0_o)) {
        fprintf(stderr, "SISAL runtime error: 'for initial' loop in LoopB_12034 executed 0 times (guard false on entry)\n");
        exit(1);
      }
      #endif
      while (v_TEST_12041_n__1_p0_o) {
        sisal_array_t v_BODY_12035_n__0_A = {0};
        sisal_array_t v_BODY_12035_n__0_B = {0};
        sisal_array_t v_BODY_12035_n__0_BKS = {0};
        sisal_array_t v_BODY_12035_n__26_BOTHER = {0};
        sisal_array_t v_BODY_12035_n__21_FRONT = {0};
        sisal_array_t v_BODY_12035_n__0_IPVT = {0};
        int32_t v_BODY_12035_n__25_K2 = 0;
        int32_t v_BODY_12035_n__0_N = 0;
        sisal_array_t v_BODY_12035_n__0_OLD_BOTHER = {0};
        int32_t v_BODY_12035_n__0_OLD_K2 = 0;
        sisal_array_t v_BODY_12035_n__22_REAR = {0};
        int32_t v_BODY_12035_n__3_T2 = 0;
        double v_BODY_12035_n__11_T3 = 0;
        sisal_array_t v_BODY_12035_n__9_TBOTHER = {0};
        sisal_array_t v_BODY_12035_n__12_TRANS_A = {0};
        sisal_array_t v_BODY_12035_n__0_p3_o = {0};
        int32_t v_BODY_12035_n__0_p5_o = 0;
        (v_BODY_12035_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_A));
        (v_BODY_12035_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_B));
        (v_BODY_12035_n__0_BKS = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_BKS));
        (v_BODY_12035_n__0_p3_o = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__5_MERGE_BOTHER));
        (v_BODY_12035_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_IPVT));
        (v_BODY_12035_n__0_p5_o = SISAL_CAST(int32_t, v_LoopB_12034_n__6_MERGE_K2));
        (v_BODY_12035_n__0_N = SISAL_CAST(int32_t, v_LoopB_12034_n__0_N));
        (v_BODY_12035_n__0_OLD_BOTHER = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__7_MERGE_OLD_BOTHER));
        (v_BODY_12035_n__0_OLD_K2 = SISAL_CAST(int32_t, v_LoopB_12034_n__8_MERGE_OLD_K2));
        int32_t v_BODY_12035_n__1_p0_o = 0;
        (v_BODY_12035_n__1_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_12035_n__2_p0_o = 0;
        (v_BODY_12035_n__2_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12035_n__0_N) + SISAL_CAST(int32_t, v_BODY_12035_n__1_p0_o))));
        (v_BODY_12035_n__3_T2 = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12035_n__2_p0_o) - SISAL_CAST(int32_t, v_BODY_12035_n__0_OLD_K2))));
        float v_BODY_12035_n__4_p0_o = 0;
        (v_BODY_12035_n__4_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_OLD_BOTHER).data)[(SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_OLD_BOTHER).lower_bound[0])]));
        double v_BODY_12035_n__5_p0_o = 0;
        (v_BODY_12035_n__5_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_OLD_BOTHER).data)[(SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_OLD_BOTHER).lower_bound[0])]));
        sisal_array_t v_BODY_12035_n__6_p0_o = {0};
        (v_BODY_12035_n__6_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_A), (SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_A).lower_bound[0]))));
        double v_BODY_12035_n__7_p0_o = 0;
        (v_BODY_12035_n__7_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_12035_n__6_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__6_p0_o).lower_bound[0])]));
        double v_BODY_12035_n__8_p0_o = 0;
        (v_BODY_12035_n__8_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_12035_n__5_p0_o) / SISAL_CAST(double, v_BODY_12035_n__7_p0_o))));
        (v_BODY_12035_n__9_TBOTHER = SISAL_CAST(sisal_array_t, sisal_array_replace_f64(SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_OLD_BOTHER), ((int64_t)SISAL_CAST(int32_t, v_BODY_12035_n__3_T2)), SISAL_CAST(double, SISAL_CAST(double, v_BODY_12035_n__8_p0_o)))));
        double v_BODY_12035_n__10_p0_o = 0;
        (v_BODY_12035_n__10_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_12035_n__9_TBOTHER).data)[(SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__9_TBOTHER).lower_bound[0])]));
        (v_BODY_12035_n__11_T3 = SISAL_CAST(double, (-SISAL_CAST(double, v_BODY_12035_n__10_p0_o))));
        (v_BODY_12035_n__12_TRANS_A = SISAL_CAST(sisal_array_t, func_TRANSPOSE(SISAL_CAST(sisal_array_t, v_BODY_12035_n__0_A))));
        int32_t v_BODY_12035_n__13_p0_o = 0;
        (v_BODY_12035_n__13_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_12035_n__14_p0_o = 0;
        (v_BODY_12035_n__14_p0_o = SISAL_CAST(int32_t, 1));
        float v_BODY_12035_n__15_p0_o = 0;
        (v_BODY_12035_n__15_p0_o = SISAL_CAST(float, (SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(int32_t, v_BODY_12035_n__14_p0_o))));
        float v_BODY_12035_n__16_p0_o = 0;
        (v_BODY_12035_n__16_p0_o = SISAL_CAST(float, ((float *)SISAL_CAST(sisal_array_t, v_BODY_12035_n__12_TRANS_A).data)[(SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__12_TRANS_A).lower_bound[0])]));
        int32_t v_BODY_12035_n__17_p0_o = 0;
        (v_BODY_12035_n__17_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_12035_n__18_p0_o = 0;
        (v_BODY_12035_n__18_p0_o = SISAL_CAST(int32_t, 1));
        int32_t v_BODY_12035_n__19_p0_o = 0;
        (v_BODY_12035_n__19_p0_o = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(int32_t, v_BODY_12035_n__18_p0_o))));
        sisal_array_t v_BODY_12035_n__20_p0_o = {0};
        (v_BODY_12035_n__20_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_12035_n__12_TRANS_A), (SISAL_CAST(int32_t, v_BODY_12035_n__3_T2) - SISAL_CAST(sisal_array_t, v_BODY_12035_n__12_TRANS_A).lower_bound[0]))));
        (v_BODY_12035_n__21_FRONT = SISAL_CAST(sisal_array_t, func_SAXPY(SISAL_CAST(int32_t, v_BODY_12035_n__17_p0_o), SISAL_CAST(int32_t, v_BODY_12035_n__19_p0_o), SISAL_CAST(double, v_BODY_12035_n__11_T3), SISAL_CAST(sisal_array_t, v_BODY_12035_n__20_p0_o), SISAL_CAST(sisal_array_t, v_BODY_12035_n__9_TBOTHER))));
        {
          sisal_array_t v_FORALL_12036_n__0_A = v_BODY_12035_n__0_A;
          sisal_array_t v_FORALL_12036_n__0_B = v_BODY_12035_n__0_B;
          sisal_array_t v_FORALL_12036_n__0_BKS = v_BODY_12035_n__0_BKS;
          sisal_array_t v_FORALL_12036_n__0_BOTHER = v_BODY_12035_n__0_p3_o;
          sisal_array_t v_FORALL_12036_n__0_FRONT = v_BODY_12035_n__21_FRONT;
          int32_t v_FORALL_12036_n__2_I;
          sisal_array_t v_FORALL_12036_n__0_IPVT = v_BODY_12035_n__0_IPVT;
          int32_t v_FORALL_12036_n__0_K2 = v_BODY_12035_n__0_p5_o;
          int32_t v_FORALL_12036_n__0_N = v_BODY_12035_n__0_N;
          sisal_array_t v_FORALL_12036_n__0_OLD_BOTHER = v_BODY_12035_n__0_OLD_BOTHER;
          int32_t v_FORALL_12036_n__0_OLD_K2 = v_BODY_12035_n__0_OLD_K2;
          int32_t v_FORALL_12036_n__0_T2 = v_BODY_12035_n__3_T2;
          double v_FORALL_12036_n__0_T3 = v_BODY_12035_n__11_T3;
          sisal_array_t v_FORALL_12036_n__0_TBOTHER = v_BODY_12035_n__9_TBOTHER;
          sisal_array_t v_FORALL_12036_n__0_TRANS_A = v_BODY_12035_n__12_TRANS_A;
          double v_FORALL_12036_n__3___forall_body_0;
          int32_t v_FORALL_12036_n__2___forall_lb_1_0;
          int32_t v_FORALL_12036_n__2___forall_ub_1_0;
          sisal_array_t v_GENERATOR_12038_n__0_A;
          sisal_array_t v_GENERATOR_12038_n__0_B;
          sisal_array_t v_GENERATOR_12038_n__0_BKS;
          sisal_array_t v_GENERATOR_12038_n__0_BOTHER;
          sisal_array_t v_GENERATOR_12038_n__0_FRONT;
          int32_t v_GENERATOR_12038_n__1_I;
          sisal_array_t v_GENERATOR_12038_n__0_IPVT;
          int32_t v_GENERATOR_12038_n__0_K2;
          int32_t v_GENERATOR_12038_n__0_N;
          sisal_array_t v_GENERATOR_12038_n__0_OLD_BOTHER;
          int32_t v_GENERATOR_12038_n__0_OLD_K2;
          int32_t v_GENERATOR_12038_n__0_T2;
          double v_GENERATOR_12038_n__0_T3;
          sisal_array_t v_GENERATOR_12038_n__0_TBOTHER;
          sisal_array_t v_GENERATOR_12038_n__0_TRANS_A;
          int32_t v_GENERATOR_12038_n__1___forall_lb_1_0;
          int32_t v_GENERATOR_12038_n__1___forall_ub_1_0;
          sisal_array_t v_BODY_12039_n__0_A;
          sisal_array_t v_BODY_12039_n__0_B;
          sisal_array_t v_BODY_12039_n__0_BKS;
          sisal_array_t v_BODY_12039_n__0_BOTHER;
          sisal_array_t v_BODY_12039_n__0_FRONT;
          int32_t v_BODY_12039_n__0_I;
          sisal_array_t v_BODY_12039_n__0_IPVT;
          int32_t v_BODY_12039_n__0_K2;
          int32_t v_BODY_12039_n__0_N;
          sisal_array_t v_BODY_12039_n__0_OLD_BOTHER;
          int32_t v_BODY_12039_n__0_OLD_K2;
          int32_t v_BODY_12039_n__0_T2;
          double v_BODY_12039_n__0_T3;
          sisal_array_t v_BODY_12039_n__0_TBOTHER;
          sisal_array_t v_BODY_12039_n__0_TRANS_A;
          int32_t v_BODY_12039_n__0___forall_lb_1_0;
          int32_t v_BODY_12039_n__0___forall_ub_1_0;
          (v_GENERATOR_12038_n__0_N = v_FORALL_12036_n__0_N);
          (v_GENERATOR_12038_n__0_T2 = v_FORALL_12036_n__0_T2);
          (v_BODY_12035_n__22_REAR = sisal_array_alloc_empty(1, 4, ((uint64_t)(1 * ((v_GENERATOR_12038_n__0_N - v_GENERATOR_12038_n__0_T2) + 1)))));
          (v_BODY_12035_n__22_REAR.dims[0] = ((v_GENERATOR_12038_n__0_N - v_GENERATOR_12038_n__0_T2) + 1));
          (v_BODY_12035_n__22_REAR.lower_bound[0] = v_GENERATOR_12038_n__0_T2);
          int32_t __g_12036 = 0;
          (v_GENERATOR_12038_n__1___forall_lb_1_0 = v_GENERATOR_12038_n__0_T2);
          (v_GENERATOR_12038_n__1___forall_ub_1_0 = v_GENERATOR_12038_n__0_N);
          for ((v_GENERATOR_12038_n__1_I = v_GENERATOR_12038_n__0_T2); (v_GENERATOR_12038_n__1_I <= v_GENERATOR_12038_n__0_N); (v_GENERATOR_12038_n__1_I++)) {
            (v_BODY_12039_n__0_A = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_A));
            (v_BODY_12039_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_B));
            (v_BODY_12039_n__0_BKS = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_BKS));
            (v_BODY_12039_n__0_BOTHER = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_BOTHER));
            (v_BODY_12039_n__0_FRONT = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_FRONT));
            (v_BODY_12039_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_12038_n__1_I));
            (v_BODY_12039_n__0_IPVT = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_IPVT));
            (v_BODY_12039_n__0_K2 = SISAL_CAST(int32_t, v_FORALL_12036_n__0_K2));
            (v_BODY_12039_n__0_N = SISAL_CAST(int32_t, v_FORALL_12036_n__0_N));
            (v_BODY_12039_n__0_OLD_BOTHER = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_OLD_BOTHER));
            (v_BODY_12039_n__0_OLD_K2 = SISAL_CAST(int32_t, v_FORALL_12036_n__0_OLD_K2));
            (v_BODY_12039_n__0_T2 = SISAL_CAST(int32_t, v_FORALL_12036_n__0_T2));
            (v_BODY_12039_n__0_T3 = SISAL_CAST(double, v_FORALL_12036_n__0_T3));
            (v_BODY_12039_n__0_TBOTHER = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_TBOTHER));
            (v_BODY_12039_n__0_TRANS_A = SISAL_CAST(sisal_array_t, v_FORALL_12036_n__0_TRANS_A));
            (v_BODY_12039_n__0___forall_lb_1_0 = SISAL_CAST(int32_t, v_GENERATOR_12038_n__1___forall_lb_1_0));
            (v_BODY_12039_n__0___forall_ub_1_0 = SISAL_CAST(int32_t, v_GENERATOR_12038_n__1___forall_ub_1_0));
            double v_BODY_12039_n__1_p0_o = 0;
            (v_BODY_12039_n__1_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_12039_n__0_TBOTHER).data)[(SISAL_CAST(int32_t, v_BODY_12039_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_12039_n__0_TBOTHER).lower_bound[0])]));
            (((double *)v_BODY_12035_n__22_REAR.data)[__g_12036] = SISAL_CAST(double, v_BODY_12039_n__1_p0_o));
            (__g_12036++);
          }
        }
        int32_t v_BODY_12035_n__24_p0_o = 0;
        (v_BODY_12035_n__24_p0_o = SISAL_CAST(int32_t, 1));
        (v_BODY_12035_n__25_K2 = SISAL_CAST(int32_t, (SISAL_CAST(int32_t, v_BODY_12035_n__0_OLD_K2) + SISAL_CAST(int32_t, v_BODY_12035_n__24_p0_o))));
        (v_BODY_12035_n__26_BOTHER = SISAL_CAST(sisal_array_t, sisal_array_addh_arr(SISAL_CAST(sisal_array_t, v_BODY_12035_n__21_FRONT), SISAL_CAST(sisal_array_t, v_BODY_12035_n__22_REAR))));
        bool v_BODY_12035_n__27_p0_o = 0;
        (v_BODY_12035_n__27_p0_o = SISAL_CAST(bool, false));
        (v_LoopB_12034_bodycap_n25_p0 = v_BODY_12035_n__25_K2);
        (v_LoopB_12034_bodycap_n26_p0 = v_BODY_12035_n__26_BOTHER);
        (v_LoopB_12034_bodycap_n27_p0 = v_BODY_12035_n__27_p0_o);
        (v_LoopB_12034_n__5_MERGE_BOTHER = v_LoopB_12034_bodycap_n26_p0);
        (v_LoopB_12034_n__6_MERGE_K2 = v_LoopB_12034_bodycap_n25_p0);
        (v_LoopB_12034_n__7_MERGE_OLD_BOTHER = v_LoopB_12034_bodycap_n26_p0);
        (v_LoopB_12034_n__8_MERGE_OLD_K2 = v_LoopB_12034_bodycap_n25_p0);
        (v_LoopB_12034_n__9_MERGE_first = v_LoopB_12034_bodycap_n27_p0);
        (v_TEST_12041_n__0_A = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_A));
        (v_TEST_12041_n__0_B = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_B));
        (v_TEST_12041_n__0_BKS = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_BKS));
        (v_TEST_12041_n__0_BOTHER = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__5_MERGE_BOTHER));
        (v_TEST_12041_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__0_IPVT));
        (v_TEST_12041_n__0_K2 = SISAL_CAST(int32_t, v_LoopB_12034_n__6_MERGE_K2));
        (v_TEST_12041_n__0_N = SISAL_CAST(int32_t, v_LoopB_12034_n__0_N));
        (v_TEST_12041_n__0_OLD_BOTHER = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__7_MERGE_OLD_BOTHER));
        (v_TEST_12041_n__0_OLD_K2 = SISAL_CAST(int32_t, v_LoopB_12034_n__8_MERGE_OLD_K2));
        (v_TEST_12041_n__1_p0_o = SISAL_CAST(bool, (SISAL_CAST(int32_t, v_TEST_12041_n__0_K2) <= SISAL_CAST(int32_t, v_TEST_12041_n__0_N))));
      }
      sisal_array_t v_RETURNS_12040_n__0_p0_o = {0};
      (v_RETURNS_12040_n__0_p0_o = SISAL_CAST(sisal_array_t, v_LoopB_12034_n__7_MERGE_OLD_BOTHER));
      sisal_array_t v_RETURNS_12040_n__1_p0_o = {0};
      (v_RETURNS_12040_n__1_p0_o = SISAL_CAST(sisal_array_t, SISAL_CAST(sisal_array_t, v_RETURNS_12040_n__0_p0_o)));
      (v_LET_NON_REC_12020_n__3_p0_o = SISAL_CAST(sisal_array_t, v_RETURNS_12040_n__1_p0_o));
    }
    (v_g14_n__1_p0_o = SISAL_CAST(sisal_array_t, v_LET_NON_REC_12020_n__3_p0_o));
  }
  (v_g14_n__0_p0_i = SISAL_CAST(sisal_array_t, v_g14_n__1_p0_o));
  return SISAL_CAST(sisal_array_t, v_g14_n__0_p0_i);
}

extern "C" double func_CALC_RESID(sisal_array_t HILB, int32_t N, int32_t LDA, sisal_array_t B) {
  sisal_array_t v_g15_n__0_B = {0};
  sisal_array_t v_g15_n__0_HILB = {0};
  int32_t v_g15_n__0_LDA = 0;
  int32_t v_g15_n__0_N = 0;
  (v_g15_n__0_HILB = SISAL_CAST(sisal_array_t, HILB));
  (v_g15_n__0_N = SISAL_CAST(int32_t, N));
  (v_g15_n__0_LDA = SISAL_CAST(int32_t, LDA));
  (v_g15_n__0_B = SISAL_CAST(sisal_array_t, B));
  double v_g15_n__0_p0_i = 0;
  double v_g15_n__1_p0_o = 0;
  {
    sisal_array_t v_LET_NON_REC_11002_n__0_B = {0};
    sisal_array_t v_LET_NON_REC_11002_n__0_HILB = {0};
    sisal_array_t v_LET_NON_REC_11002_n__2_HILB1 = {0};
    sisal_array_t v_LET_NON_REC_11002_n__2_IPVT = {0};
    int32_t v_LET_NON_REC_11002_n__0_LDA = 0;
    int32_t v_LET_NON_REC_11002_n__0_N = 0;
    double v_LET_NON_REC_11002_n__2_RCOND = 0;
    double v_LET_NON_REC_11002_n__4_RESID = 0;
    sisal_array_t v_LET_NON_REC_11002_n__2_WORK = {0};
    (v_LET_NON_REC_11002_n__0_B = SISAL_CAST(sisal_array_t, v_g15_n__0_B));
    (v_LET_NON_REC_11002_n__0_HILB = SISAL_CAST(sisal_array_t, v_g15_n__0_HILB));
    (v_LET_NON_REC_11002_n__0_LDA = SISAL_CAST(int32_t, v_g15_n__0_LDA));
    (v_LET_NON_REC_11002_n__0_N = SISAL_CAST(int32_t, v_g15_n__0_N));
    struct FUNC_SGECO_results _mr_LET_NON_REC_11002_1 = func_SGECO(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11002_n__0_HILB), SISAL_CAST(int32_t, v_LET_NON_REC_11002_n__0_LDA), SISAL_CAST(int32_t, v_LET_NON_REC_11002_n__0_N));
    sisal_array_t v_LET_NON_REC_11002_n__1_p0_o = {0};
    (v_LET_NON_REC_11002_n__1_p0_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_11002_1.res_0));
    sisal_array_t v_LET_NON_REC_11002_n__1_p1_o = {0};
    (v_LET_NON_REC_11002_n__1_p1_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_11002_1.res_1));
    double v_LET_NON_REC_11002_n__1_p2_o = 0;
    (v_LET_NON_REC_11002_n__1_p2_o = SISAL_CAST(double, _mr_LET_NON_REC_11002_1.res_2));
    sisal_array_t v_LET_NON_REC_11002_n__1_p3_o = {0};
    (v_LET_NON_REC_11002_n__1_p3_o = SISAL_CAST(sisal_array_t, _mr_LET_NON_REC_11002_1.res_3));
    double v_LET_NON_REC_11002_n__3_p0_o = 0;
    double v_IF_DOUBLE___11003_n__0_RCOND = 0;
    (v_IF_DOUBLE___11003_n__0_RCOND = SISAL_CAST(double, v_LET_NON_REC_11002_n__1_p2_o));
    sisal_array_t v_IF_DOUBLE___11003_n__0_B = {0};
    (v_IF_DOUBLE___11003_n__0_B = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11002_n__0_B));
    sisal_array_t v_IF_DOUBLE___11003_n__0_HILB = {0};
    (v_IF_DOUBLE___11003_n__0_HILB = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11002_n__0_HILB));
    sisal_array_t v_IF_DOUBLE___11003_n__0_HILB1 = {0};
    (v_IF_DOUBLE___11003_n__0_HILB1 = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11002_n__1_p0_o));
    sisal_array_t v_IF_DOUBLE___11003_n__0_IPVT = {0};
    (v_IF_DOUBLE___11003_n__0_IPVT = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11002_n__1_p1_o));
    int32_t v_IF_DOUBLE___11003_n__0_LDA = 0;
    (v_IF_DOUBLE___11003_n__0_LDA = SISAL_CAST(int32_t, v_LET_NON_REC_11002_n__0_LDA));
    int32_t v_IF_DOUBLE___11003_n__0_N = 0;
    (v_IF_DOUBLE___11003_n__0_N = SISAL_CAST(int32_t, v_LET_NON_REC_11002_n__0_N));
    sisal_array_t v_IF_DOUBLE___11003_n__0_WORK = {0};
    (v_IF_DOUBLE___11003_n__0_WORK = SISAL_CAST(sisal_array_t, v_LET_NON_REC_11002_n__1_p3_o));
    {
      double v_PREDICATE_11004_n__0_RCOND = 0;
      (v_PREDICATE_11004_n__0_RCOND = SISAL_CAST(double, v_IF_DOUBLE___11003_n__0_RCOND));
      double v_PREDICATE_11004_n__1_p0_o = 0;
      (v_PREDICATE_11004_n__1_p0_o = SISAL_CAST(double, 0.));
      bool v_PREDICATE_11004_n__2_p0_o = 0;
      (v_PREDICATE_11004_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_11004_n__0_RCOND) == SISAL_CAST(double, v_PREDICATE_11004_n__1_p0_o))));
      if (v_PREDICATE_11004_n__2_p0_o) {
        double v_THEN_11015_n__1_p0_o = 0;
        (v_THEN_11015_n__1_p0_o = SISAL_CAST(double, 999.));
        double v_THEN_11015_n__2_p0_o = 0;
        (v_THEN_11015_n__2_p0_o = SISAL_CAST(double, (-SISAL_CAST(double, v_THEN_11015_n__1_p0_o))));
        (v_LET_NON_REC_11002_n__3_p0_o = SISAL_CAST(double, v_THEN_11015_n__2_p0_o));
      }
      else {
        sisal_array_t v_ELSE_11005_n__0_B = {0};
        sisal_array_t v_ELSE_11005_n__0_HILB = {0};
        sisal_array_t v_ELSE_11005_n__0_HILB1 = {0};
        sisal_array_t v_ELSE_11005_n__0_IPVT = {0};
        int32_t v_ELSE_11005_n__0_LDA = 0;
        int32_t v_ELSE_11005_n__0_N = 0;
        double v_ELSE_11005_n__0_RCOND = 0;
        sisal_array_t v_ELSE_11005_n__0_WORK = {0};
        (v_ELSE_11005_n__0_B = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___11003_n__0_B));
        (v_ELSE_11005_n__0_HILB = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___11003_n__0_HILB));
        (v_ELSE_11005_n__0_HILB1 = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___11003_n__0_HILB1));
        (v_ELSE_11005_n__0_IPVT = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___11003_n__0_IPVT));
        (v_ELSE_11005_n__0_LDA = SISAL_CAST(int32_t, v_IF_DOUBLE___11003_n__0_LDA));
        (v_ELSE_11005_n__0_N = SISAL_CAST(int32_t, v_IF_DOUBLE___11003_n__0_N));
        (v_ELSE_11005_n__0_RCOND = SISAL_CAST(double, v_IF_DOUBLE___11003_n__0_RCOND));
        (v_ELSE_11005_n__0_WORK = SISAL_CAST(sisal_array_t, v_IF_DOUBLE___11003_n__0_WORK));
        double v_ELSE_11005_n__1_p0_o = 0;
        {
          sisal_array_t v_LET_NON_REC_11006_n__0_B = {0};
          sisal_array_t v_LET_NON_REC_11006_n__0_HILB = {0};
          sisal_array_t v_LET_NON_REC_11006_n__0_HILB1 = {0};
          sisal_array_t v_LET_NON_REC_11006_n__0_IPVT = {0};
          int32_t v_LET_NON_REC_11006_n__0_LDA = 0;
          int32_t v_LET_NON_REC_11006_n__0_N = 0;
          double v_LET_NON_REC_11006_n__0_RCOND = 0;
          sisal_array_t v_LET_NON_REC_11006_n__0_WORK = {0};
          sisal_array_t v_LET_NON_REC_11006_n__1_XTEMP = {0};
          (v_LET_NON_REC_11006_n__0_B = SISAL_CAST(sisal_array_t, v_ELSE_11005_n__0_B));
          (v_LET_NON_REC_11006_n__0_HILB = SISAL_CAST(sisal_array_t, v_ELSE_11005_n__0_HILB));
          (v_LET_NON_REC_11006_n__0_HILB1 = SISAL_CAST(sisal_array_t, v_ELSE_11005_n__0_HILB1));
          (v_LET_NON_REC_11006_n__0_IPVT = SISAL_CAST(sisal_array_t, v_ELSE_11005_n__0_IPVT));
          (v_LET_NON_REC_11006_n__0_LDA = SISAL_CAST(int32_t, v_ELSE_11005_n__0_LDA));
          (v_LET_NON_REC_11006_n__0_N = SISAL_CAST(int32_t, v_ELSE_11005_n__0_N));
          (v_LET_NON_REC_11006_n__0_RCOND = SISAL_CAST(double, v_ELSE_11005_n__0_RCOND));
          (v_LET_NON_REC_11006_n__0_WORK = SISAL_CAST(sisal_array_t, v_ELSE_11005_n__0_WORK));
          (v_LET_NON_REC_11006_n__1_XTEMP = SISAL_CAST(sisal_array_t, func_SGESL(SISAL_CAST(sisal_array_t, v_LET_NON_REC_11006_n__0_HILB1), SISAL_CAST(int32_t, v_LET_NON_REC_11006_n__0_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_11006_n__0_IPVT), SISAL_CAST(sisal_array_t, v_LET_NON_REC_11006_n__0_B))));
          double v_LET_NON_REC_11006_n__2_p0_o = 0;
          {
            sisal_array_t v_FORALL_11007_n__0_B = v_LET_NON_REC_11006_n__0_B;
            sisal_array_t v_FORALL_11007_n__0_HILB = v_LET_NON_REC_11006_n__0_HILB;
            sisal_array_t v_FORALL_11007_n__0_HILB1 = v_LET_NON_REC_11006_n__0_HILB1;
            int32_t v_FORALL_11007_n__2_I;
            sisal_array_t v_FORALL_11007_n__0_IPVT = v_LET_NON_REC_11006_n__0_IPVT;
            int32_t v_FORALL_11007_n__0_LDA = v_LET_NON_REC_11006_n__0_LDA;
            int32_t v_FORALL_11007_n__0_N = v_LET_NON_REC_11006_n__0_N;
            double v_FORALL_11007_n__0_RCOND = v_LET_NON_REC_11006_n__0_RCOND;
            sisal_array_t v_FORALL_11007_n__0_WORK = v_LET_NON_REC_11006_n__0_WORK;
            sisal_array_t v_FORALL_11007_n__0_XTEMP = v_LET_NON_REC_11006_n__1_XTEMP;
            double v_FORALL_11007_n__3___forall_body_0;
            int32_t v_FORALL_11007_n__2___forall_lb_2_0;
            int32_t v_FORALL_11007_n__2___forall_ub_2_0;
            sisal_array_t v_GENERATOR_11009_n__0_B;
            sisal_array_t v_GENERATOR_11009_n__0_HILB;
            sisal_array_t v_GENERATOR_11009_n__0_HILB1;
            int32_t v_GENERATOR_11009_n__2_I;
            sisal_array_t v_GENERATOR_11009_n__0_IPVT;
            int32_t v_GENERATOR_11009_n__0_LDA;
            int32_t v_GENERATOR_11009_n__0_N;
            double v_GENERATOR_11009_n__0_RCOND;
            sisal_array_t v_GENERATOR_11009_n__0_WORK;
            sisal_array_t v_GENERATOR_11009_n__0_XTEMP;
            int32_t v_GENERATOR_11009_n__2___forall_lb_2_0;
            int32_t v_GENERATOR_11009_n__2___forall_ub_2_0;
            sisal_array_t v_BODY_11010_n__0_B;
            sisal_array_t v_BODY_11010_n__0_HILB;
            sisal_array_t v_BODY_11010_n__0_HILB1;
            double v_BODY_11010_n__1_HPROD;
            double v_BODY_11010_n__4_HPROD1;
            int32_t v_BODY_11010_n__0_I;
            sisal_array_t v_BODY_11010_n__0_IPVT;
            int32_t v_BODY_11010_n__0_LDA;
            int32_t v_BODY_11010_n__0_N;
            double v_BODY_11010_n__0_RCOND;
            sisal_array_t v_BODY_11010_n__0_WORK;
            sisal_array_t v_BODY_11010_n__0_XTEMP;
            int32_t v_BODY_11010_n__0___forall_lb_2_0;
            int32_t v_BODY_11010_n__0___forall_ub_2_0;
            sisal_array_t v_FORALL_11011_n__0_B;
            sisal_array_t v_FORALL_11011_n__0_HILB;
            sisal_array_t v_FORALL_11011_n__0_HILB1;
            int32_t v_FORALL_11011_n__0_I;
            sisal_array_t v_FORALL_11011_n__0_IPVT;
            int32_t v_FORALL_11011_n__2_J;
            int32_t v_FORALL_11011_n__0_LDA;
            int32_t v_FORALL_11011_n__0_N;
            double v_FORALL_11011_n__0_RCOND;
            sisal_array_t v_FORALL_11011_n__0_WORK;
            sisal_array_t v_FORALL_11011_n__0_XTEMP;
            double v_FORALL_11011_n__3___forall_body_0;
            int32_t v_FORALL_11011_n__2___forall_lb_2_0;
            int32_t v_FORALL_11011_n__2___forall_ub_2_0;
            sisal_array_t v_GENERATOR_11013_n__0_B;
            sisal_array_t v_GENERATOR_11013_n__0_HILB;
            sisal_array_t v_GENERATOR_11013_n__0_HILB1;
            int32_t v_GENERATOR_11013_n__0_I;
            sisal_array_t v_GENERATOR_11013_n__0_IPVT;
            int32_t v_GENERATOR_11013_n__2_J;
            int32_t v_GENERATOR_11013_n__0_LDA;
            int32_t v_GENERATOR_11013_n__0_N;
            double v_GENERATOR_11013_n__0_RCOND;
            sisal_array_t v_GENERATOR_11013_n__0_WORK;
            sisal_array_t v_GENERATOR_11013_n__0_XTEMP;
            int32_t v_GENERATOR_11013_n__2___forall_lb_2_0;
            int32_t v_GENERATOR_11013_n__2___forall_ub_2_0;
            sisal_array_t v_BODY_11014_n__0_B;
            sisal_array_t v_BODY_11014_n__0_HILB;
            sisal_array_t v_BODY_11014_n__0_HILB1;
            int32_t v_BODY_11014_n__0_I;
            sisal_array_t v_BODY_11014_n__0_IPVT;
            int32_t v_BODY_11014_n__0_J;
            int32_t v_BODY_11014_n__0_LDA;
            int32_t v_BODY_11014_n__0_N;
            double v_BODY_11014_n__0_RCOND;
            sisal_array_t v_BODY_11014_n__0_WORK;
            sisal_array_t v_BODY_11014_n__0_XTEMP;
            int32_t v_BODY_11014_n__0___forall_lb_2_0;
            int32_t v_BODY_11014_n__0___forall_ub_2_0;
            (v_GENERATOR_11009_n__0_N = v_FORALL_11007_n__0_N);
            (v_LET_NON_REC_11006_n__2_p0_o = 0);
            (v_GENERATOR_11009_n__2___forall_lb_2_0 = 1);
            (v_GENERATOR_11009_n__2___forall_ub_2_0 = v_GENERATOR_11009_n__0_N);
            for ((v_GENERATOR_11009_n__2_I = 1); (v_GENERATOR_11009_n__2_I <= v_GENERATOR_11009_n__0_N); (v_GENERATOR_11009_n__2_I++)) {
              (v_BODY_11010_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11007_n__0_B));
              (v_BODY_11010_n__0_HILB = SISAL_CAST(sisal_array_t, v_FORALL_11007_n__0_HILB));
              (v_BODY_11010_n__0_HILB1 = SISAL_CAST(sisal_array_t, v_FORALL_11007_n__0_HILB1));
              (v_BODY_11010_n__0_I = SISAL_CAST(int32_t, v_GENERATOR_11009_n__2_I));
              (v_BODY_11010_n__0_IPVT = SISAL_CAST(sisal_array_t, v_FORALL_11007_n__0_IPVT));
              (v_BODY_11010_n__0_LDA = SISAL_CAST(int32_t, v_FORALL_11007_n__0_LDA));
              (v_BODY_11010_n__0_N = SISAL_CAST(int32_t, v_FORALL_11007_n__0_N));
              (v_BODY_11010_n__0_RCOND = SISAL_CAST(double, v_FORALL_11007_n__0_RCOND));
              (v_BODY_11010_n__0_WORK = SISAL_CAST(sisal_array_t, v_FORALL_11007_n__0_WORK));
              (v_BODY_11010_n__0_XTEMP = SISAL_CAST(sisal_array_t, v_FORALL_11007_n__0_XTEMP));
              (v_BODY_11010_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_11009_n__2___forall_lb_2_0));
              (v_BODY_11010_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_11009_n__2___forall_ub_2_0));
              {
                sisal_array_t v_FORALL_11011_n__0_B = v_BODY_11010_n__0_B;
                sisal_array_t v_FORALL_11011_n__0_HILB = v_BODY_11010_n__0_HILB;
                sisal_array_t v_FORALL_11011_n__0_HILB1 = v_BODY_11010_n__0_HILB1;
                int32_t v_FORALL_11011_n__0_I = v_BODY_11010_n__0_I;
                sisal_array_t v_FORALL_11011_n__0_IPVT = v_BODY_11010_n__0_IPVT;
                int32_t v_FORALL_11011_n__2_J;
                int32_t v_FORALL_11011_n__0_LDA = v_BODY_11010_n__0_LDA;
                int32_t v_FORALL_11011_n__0_N = v_BODY_11010_n__0_N;
                double v_FORALL_11011_n__0_RCOND = v_BODY_11010_n__0_RCOND;
                sisal_array_t v_FORALL_11011_n__0_WORK = v_BODY_11010_n__0_WORK;
                sisal_array_t v_FORALL_11011_n__0_XTEMP = v_BODY_11010_n__0_XTEMP;
                double v_FORALL_11011_n__3___forall_body_0;
                int32_t v_FORALL_11011_n__2___forall_lb_2_0;
                int32_t v_FORALL_11011_n__2___forall_ub_2_0;
                sisal_array_t v_GENERATOR_11013_n__0_B;
                sisal_array_t v_GENERATOR_11013_n__0_HILB;
                sisal_array_t v_GENERATOR_11013_n__0_HILB1;
                int32_t v_GENERATOR_11013_n__0_I;
                sisal_array_t v_GENERATOR_11013_n__0_IPVT;
                int32_t v_GENERATOR_11013_n__2_J;
                int32_t v_GENERATOR_11013_n__0_LDA;
                int32_t v_GENERATOR_11013_n__0_N;
                double v_GENERATOR_11013_n__0_RCOND;
                sisal_array_t v_GENERATOR_11013_n__0_WORK;
                sisal_array_t v_GENERATOR_11013_n__0_XTEMP;
                int32_t v_GENERATOR_11013_n__2___forall_lb_2_0;
                int32_t v_GENERATOR_11013_n__2___forall_ub_2_0;
                sisal_array_t v_BODY_11014_n__0_B;
                sisal_array_t v_BODY_11014_n__0_HILB;
                sisal_array_t v_BODY_11014_n__0_HILB1;
                int32_t v_BODY_11014_n__0_I;
                sisal_array_t v_BODY_11014_n__0_IPVT;
                int32_t v_BODY_11014_n__0_J;
                int32_t v_BODY_11014_n__0_LDA;
                int32_t v_BODY_11014_n__0_N;
                double v_BODY_11014_n__0_RCOND;
                sisal_array_t v_BODY_11014_n__0_WORK;
                sisal_array_t v_BODY_11014_n__0_XTEMP;
                int32_t v_BODY_11014_n__0___forall_lb_2_0;
                int32_t v_BODY_11014_n__0___forall_ub_2_0;
                int32_t v_FORALL_11011_n__0_p11_o = v_BODY_11010_n__0___forall_lb_2_0;
                int32_t v_FORALL_11011_n__0_p12_o = v_BODY_11010_n__0___forall_ub_2_0;
                (v_GENERATOR_11013_n__0_N = v_FORALL_11011_n__0_N);
                (v_BODY_11010_n__1_HPROD = 0);
                (v_GENERATOR_11013_n__2___forall_lb_2_0 = 1);
                (v_GENERATOR_11013_n__2___forall_ub_2_0 = v_GENERATOR_11013_n__0_N);
                for ((v_GENERATOR_11013_n__2_J = 1); (v_GENERATOR_11013_n__2_J <= v_GENERATOR_11013_n__0_N); (v_GENERATOR_11013_n__2_J++)) {
                  (v_BODY_11014_n__0_B = SISAL_CAST(sisal_array_t, v_FORALL_11011_n__0_B));
                  (v_BODY_11014_n__0_HILB = SISAL_CAST(sisal_array_t, v_FORALL_11011_n__0_HILB));
                  (v_BODY_11014_n__0_HILB1 = SISAL_CAST(sisal_array_t, v_FORALL_11011_n__0_HILB1));
                  (v_BODY_11014_n__0_I = SISAL_CAST(int32_t, v_FORALL_11011_n__0_I));
                  (v_BODY_11014_n__0_IPVT = SISAL_CAST(sisal_array_t, v_FORALL_11011_n__0_IPVT));
                  (v_BODY_11014_n__0_J = SISAL_CAST(int32_t, v_GENERATOR_11013_n__2_J));
                  (v_BODY_11014_n__0_LDA = SISAL_CAST(int32_t, v_FORALL_11011_n__0_LDA));
                  (v_BODY_11014_n__0_N = SISAL_CAST(int32_t, v_FORALL_11011_n__0_N));
                  (v_BODY_11014_n__0_RCOND = SISAL_CAST(double, v_FORALL_11011_n__0_RCOND));
                  (v_BODY_11014_n__0_WORK = SISAL_CAST(sisal_array_t, v_FORALL_11011_n__0_WORK));
                  (v_BODY_11014_n__0_XTEMP = SISAL_CAST(sisal_array_t, v_FORALL_11011_n__0_XTEMP));
                  (v_BODY_11014_n__0___forall_lb_2_0 = SISAL_CAST(int32_t, v_GENERATOR_11013_n__2___forall_lb_2_0));
                  (v_BODY_11014_n__0___forall_ub_2_0 = SISAL_CAST(int32_t, v_GENERATOR_11013_n__2___forall_ub_2_0));
                  sisal_array_t v_BODY_11014_n__1_p0_o = {0};
                  (v_BODY_11014_n__1_p0_o = SISAL_CAST(sisal_array_t, sisal_array_get_row(SISAL_CAST(sisal_array_t, v_BODY_11014_n__0_HILB), (SISAL_CAST(int32_t, v_BODY_11014_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_11014_n__0_HILB).lower_bound[0]))));
                  double v_BODY_11014_n__2_p0_o = 0;
                  (v_BODY_11014_n__2_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11014_n__1_p0_o).data)[(SISAL_CAST(int32_t, v_BODY_11014_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11014_n__1_p0_o).lower_bound[0])]));
                  double v_BODY_11014_n__3_p0_o = 0;
                  (v_BODY_11014_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11014_n__0_XTEMP).data)[(SISAL_CAST(int32_t, v_BODY_11014_n__0_J) - SISAL_CAST(sisal_array_t, v_BODY_11014_n__0_XTEMP).lower_bound[0])]));
                  double v_BODY_11014_n__4_p0_o = 0;
                  (v_BODY_11014_n__4_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11014_n__2_p0_o) * SISAL_CAST(double, v_BODY_11014_n__3_p0_o))));
                  (v_BODY_11010_n__1_HPROD = (v_BODY_11010_n__1_HPROD + SISAL_CAST(double, v_BODY_11014_n__4_p0_o)));
                }
              }
              double v_BODY_11010_n__3_p0_o = 0;
              (v_BODY_11010_n__3_p0_o = SISAL_CAST(double, ((double *)SISAL_CAST(sisal_array_t, v_BODY_11010_n__0_B).data)[(SISAL_CAST(int32_t, v_BODY_11010_n__0_I) - SISAL_CAST(sisal_array_t, v_BODY_11010_n__0_B).lower_bound[0])]));
              (v_BODY_11010_n__4_HPROD1 = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11010_n__1_HPROD) - SISAL_CAST(double, v_BODY_11010_n__3_p0_o))));
              double v_BODY_11010_n__5_p0_o = 0;
              (v_BODY_11010_n__5_p0_o = SISAL_CAST(double, (SISAL_CAST(double, v_BODY_11010_n__4_HPROD1) * SISAL_CAST(double, v_BODY_11010_n__4_HPROD1))));
              (v_LET_NON_REC_11006_n__2_p0_o = (v_LET_NON_REC_11006_n__2_p0_o + SISAL_CAST(double, v_BODY_11010_n__5_p0_o)));
            }
          }
          (v_ELSE_11005_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_11006_n__2_p0_o));
        }
        (v_LET_NON_REC_11002_n__3_p0_o = SISAL_CAST(double, v_ELSE_11005_n__1_p0_o));
      }
    }
    double v_LET_NON_REC_11002_n__5_p0_o = 0;
    double v_IF_DOUBLE___11016_n__0_RESID = 0;
    (v_IF_DOUBLE___11016_n__0_RESID = SISAL_CAST(double, v_LET_NON_REC_11002_n__3_p0_o));
    {
      double v_PREDICATE_11017_n__0_RESID = 0;
      (v_PREDICATE_11017_n__0_RESID = SISAL_CAST(double, v_IF_DOUBLE___11016_n__0_RESID));
      double v_PREDICATE_11017_n__1_p0_o = 0;
      (v_PREDICATE_11017_n__1_p0_o = SISAL_CAST(double, 0.));
      bool v_PREDICATE_11017_n__2_p0_o = 0;
      (v_PREDICATE_11017_n__2_p0_o = SISAL_CAST(bool, (SISAL_CAST(double, v_PREDICATE_11017_n__0_RESID) < SISAL_CAST(double, v_PREDICATE_11017_n__1_p0_o))));
      if (v_PREDICATE_11017_n__2_p0_o) {
        double v_THEN_11019_n__0_RESID = 0;
        (v_THEN_11019_n__0_RESID = SISAL_CAST(double, v_IF_DOUBLE___11016_n__0_RESID));
        (v_LET_NON_REC_11002_n__5_p0_o = SISAL_CAST(double, v_THEN_11019_n__0_RESID));
      }
      else {
        double v_ELSE_11018_n__0_RESID = 0;
        (v_ELSE_11018_n__0_RESID = SISAL_CAST(double, v_IF_DOUBLE___11016_n__0_RESID));
        double v_ELSE_11018_n__1_p0_o = 0;
        (v_ELSE_11018_n__1_p0_o = SISAL_CAST(double, func__SSQRT__D__D(SISAL_CAST(double, v_ELSE_11018_n__0_RESID))));
        (v_LET_NON_REC_11002_n__5_p0_o = SISAL_CAST(double, v_ELSE_11018_n__1_p0_o));
      }
    }
    (v_g15_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_11002_n__5_p0_o));
  }
  (v_g15_n__0_p0_i = SISAL_CAST(double, v_g15_n__1_p0_o));
  return SISAL_CAST(double, v_g15_n__0_p0_i);
}

extern "C" double func_MAIN(sisal_array_t HILBERT, sisal_array_t B) {
  sisal_array_t v_g16_n__0_B = {0};
  sisal_array_t v_g16_n__0_HILBERT = {0};
  (v_g16_n__0_HILBERT = SISAL_CAST(sisal_array_t, HILBERT));
  (v_g16_n__0_B = SISAL_CAST(sisal_array_t, B));
  double v_g16_n__0_p0_i = 0;
  double v_g16_n__1_p0_o = 0;
  {
    sisal_array_t v_LET_NON_REC_10001_n__0_B = {0};
    sisal_array_t v_LET_NON_REC_10001_n__0_HILBERT = {0};
    int32_t v_LET_NON_REC_10001_n__1_N = 0;
    (v_LET_NON_REC_10001_n__0_B = SISAL_CAST(sisal_array_t, v_g16_n__0_B));
    (v_LET_NON_REC_10001_n__0_HILBERT = SISAL_CAST(sisal_array_t, v_g16_n__0_HILBERT));
    (v_LET_NON_REC_10001_n__1_N = SISAL_CAST(int32_t, ((int32_t)((SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__0_HILBERT).dims[0] > 0) ? SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__0_HILBERT).dims[0] : ((int64_t)SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__0_HILBERT).size)))));
    double v_LET_NON_REC_10001_n__2_p0_o = 0;
    (v_LET_NON_REC_10001_n__2_p0_o = SISAL_CAST(double, func_CALC_RESID(SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__0_HILBERT), SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__1_N), SISAL_CAST(int32_t, v_LET_NON_REC_10001_n__1_N), SISAL_CAST(sisal_array_t, v_LET_NON_REC_10001_n__0_B))));
    (v_g16_n__1_p0_o = SISAL_CAST(double, v_LET_NON_REC_10001_n__2_p0_o));
  }
  (v_g16_n__0_p0_i = SISAL_CAST(double, v_g16_n__1_p0_o));
  return SISAL_CAST(double, v_g16_n__0_p0_i);
}
