#ifndef KIN16_REF_H
#define KIN16_REF_H
// Independent C reference for KIN16, zone electrophoresis (test/e2e/kin16_dv.sis).
//
// Transcribed from the Sisal source, not from any recorded output.  The group's
// original checks compared against magic constants carrying 15+ significant
// digits with no stated provenance; they landed in the same commit that both
// ported the test and changed the compiler, so they could only ever have
// detected CHANGE, never wrongness.  This recomputes the answer from the
// algorithm so a wrong-but-stable result is caught.
//
// Deliberately written as plain scalar C over 1-based arrays, mirroring the
// Sisal index-for-index, so it can also serve as a performance baseline later.
// `exp(x, y)` in the Sisal source is POW, not the exponential.
//
// Two transcription traps, both preserved as the source has them:
//   * the last element of each rebuilt row is `old C[m, NP]`, NOT `old C[m, N]`
//     -- the .sis comment above that line says C[1,N] but the code says NP.
//     The code is what runs.  Note this is NOT observable: OUT sums over
//     J = 2..NP, so index N is never read and the last element of every row is
//     dead.  Mutating it here changes nothing, which was verified rather than
//     assumed -- so this test cannot tell the two spellings apart, and neither
//     can the program.  Recorded so nobody later mistakes the agreement for
//     evidence that the quirk is pinned.
//   * T advances as (pre-increment I) * DT, so after IT trips T = IT*DT.

#include <cmath>
#include <vector>

namespace kin16ref {

struct Edit {
  double T, YMEANM, SIGSQM, SIGM, SUM1M, YMEANM2, SIGSQM2, SIGM2, SUM1M2;
  double DIFM, VELOCITYM, DIFM2, VELOCITYM2;
};
struct Save { double SIGSQMI, YMEANMI, SIGSQM2I, YMEANM2I; };

// C is [2][N+1], 1-based in both the row (1..2) and the column (1..N)
static inline Edit out_stage (double T, int NP, const std::vector<double> C[2],
                              const std::vector<double> &Y, Save &S)
{
  double s1 = 0, s2 = 0, s3 = 0, t1 = 0, t2 = 0, t3 = 0;
  for (int J = 2; J <= NP; J++)
    {
      const double ysq = Y[J] * Y[J];
      s1 += C[0][J]; s2 += Y[J] * C[0][J]; s3 += ysq * C[0][J];
      t1 += C[1][J]; t2 += Y[J] * C[1][J]; t3 += ysq * C[1][J];
    }
  Edit e{};
  e.T = T;
  e.SUM1M = s1;  e.YMEANM  = s2 / s1;  e.SIGSQM  = s3 / s1 - e.YMEANM * e.YMEANM;
  e.SIGM  = sqrt (e.SIGSQM);
  e.SUM1M2 = t1; e.YMEANM2 = t2 / t1;  e.SIGSQM2 = t3 / t1 - e.YMEANM2 * e.YMEANM2;
  e.SIGM2 = sqrt (e.SIGSQM2);
  if (T == 0.0)
    S = Save{ e.SIGSQM, e.YMEANM, e.SIGSQM2, e.YMEANM2 };
  if (T > 0.0)
    {
      e.DIFM       = 0.5 * (e.SIGSQM - S.SIGSQMI) / T;
      e.VELOCITYM  = (e.YMEANM - S.YMEANMI) / T;
      e.DIFM2      = 0.5 * (e.SIGSQM2 - S.SIGSQM2I) / T;
      e.VELOCITYM2 = (e.YMEANM2 - S.YMEANM2I) / T;
    }
  return e;
}

// Returns the two Edit records main() produces: at T = 0 and after IT steps.
static inline void ref_kin16 (int IT, int N, int NSEG, Edit &first, Edit &last)
{
  const int NP = N - 1, NPP = N - 2;
  const double DX = 0.7e-3, DT = 0.5;
  const double GZERO[2] = { 0.5e-5, 0.5e-5 };
  const double RK1a = 34.0;
  const double RK2a = 0.5 * RK1a * GZERO[0] * GZERO[0] / GZERO[1];
  const double RK1 = RK1a * DT, RK2 = RK2a * DT;

  // FILLUP
  std::vector<double> X (N + 1, 0.0), Y (N + 1, 0.0);
  for (int J = 2; J <= N; J++)
    { X[J] = (double)(J - 1) * DX; Y[J] = X[J] - 0.5 * DX; }
  std::vector<double> C[2] = { std::vector<double> (N + 1, 0.0),
                               std::vector<double> (N + 1, 0.0) };
  for (int m = 0; m < 2; m++)
    for (int J = 2; J <= NSEG; J++) C[m][J] = GZERO[m];

  // VELOCITY
  const double PM[2] = { -6.9018e-02, -0.10799 };
  const double T1[2] = { 6.0e-04, 5.0e-04 };
  const double T2[2] = { 2.1e-07, 1.67e-07 };
  std::vector<double> V[2] = { std::vector<double> (N + 1, 0.0),
                               std::vector<double> (N + 1, 0.0) };
  std::vector<double> DL[2] = { std::vector<double> (N + 1, 0.0),
                                std::vector<double> (N + 1, 0.0) };
  for (int m = 0; m < 2; m++)
    {
      std::vector<double> DEFF (N + 1, 0.0);
      V[m][1] = T1[m] * DT / DX;
      DEFF[1] = T2[m];
      for (int I = 2; I <= N; I++)
        {
          const double Vv = T1[m] * pow (10.0, PM[m] * X[I]);
          V[m][I] = Vv * DT / DX;
          DEFF[I] = T2[m] - 0.5 * DX * Vv + 0.5 * DT * Vv * Vv;
        }
      for (int I = 1; I <= N; I++) DL[m][I] = DEFF[I] * DT / (DX * DX);
    }

  Save S{ 0, 0, 0, 0 };
  first = out_stage (0.0, NP, C, Y, S);

  double T = 0.0;
  for (int step = 1; step <= IT; step++)
    {
      std::vector<double> nc[2] = { std::vector<double> (N + 1, 0.0),
                                    std::vector<double> (N + 1, 0.0) };
      const double c12 = C[0][2] + DL[0][2] * (C[0][3] - C[0][2])
                         - V[0][2] * C[0][2] - RK1 * C[0][2] * C[0][2]
                         + 2.0 * RK2 * C[1][2];
      const double c22 = C[1][2] + DL[1][2] * (C[1][3] - C[1][2])
                         - V[1][2] * C[1][2] + 0.5 * RK1 * C[0][2] * C[0][2]
                         - RK2 * C[1][2];
      for (int J = 3; J <= NPP; J++)
        {
          nc[0][J] = C[0][J] + DL[0][J] * (C[0][J + 1] - C[0][J])
                     - DL[0][J - 1] * (C[0][J] - C[0][J - 1])
                     - V[0][J] * C[0][J] + V[0][J - 1] * C[0][J - 1]
                     - RK1 * C[0][J] * C[0][J] + 2.0 * RK2 * C[1][J];
          nc[1][J] = C[1][J] + DL[1][J] * (C[1][J + 1] - C[1][J])
                     - DL[1][J - 1] * (C[1][J] - C[1][J - 1])
                     - V[1][J] * C[1][J] + V[1][J - 1] * C[1][J - 1]
                     + 0.5 * RK1 * C[0][J] * C[0][J] - RK2 * C[1][J];
        }
      const double c1np = C[0][NP] - DL[0][NP] * C[0][NP]
                          - DL[0][NPP] * (C[0][NP] - C[0][NPP])
                          - V[0][NP] * C[0][NP] + V[0][NPP] * C[0][NPP]
                          - RK1 * C[0][NP] * C[0][NP] + 2.0 * RK2 * C[1][NP];
      const double c2np = C[1][NP] - DL[1][NP] * C[1][NP]
                          - DL[1][NPP] * (C[1][NP] - C[1][NPP])
                          - V[1][NP] * C[1][NP] + V[1][NPP] * C[1][NPP]
                          + 0.5 * RK1 * C[0][NP] * C[0][NP] - RK2 * C[1][NP];
      nc[0][1] = C[0][1]; nc[0][2] = c12; nc[0][NP] = c1np; nc[0][N] = C[0][NP];
      nc[1][1] = C[1][1]; nc[1][2] = c22; nc[1][NP] = c2np; nc[1][N] = C[1][NP];
      C[0] = nc[0]; C[1] = nc[1];
      T = (double)step * DT;
    }
  last = out_stage (T, NP, C, Y, S);
}

}  // namespace kin16ref
#endif
