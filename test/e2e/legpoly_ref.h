#ifndef LEGPOLY_REF_H
#define LEGPOLY_REF_H
// Independent C reference for LegendrePolyOf1stKind (test/e2e/legpoly_dv_e2e.sis).
//
// Transcribed from the Sisal source.  The group previously compared against
// eight constants of 6-8 significant digits with no provenance, reading 9 of
// the 16 result elements at a single input -- and that input was ir = 2, which
// takes the `IF ir = 2 THEN pp` short-circuit, so the ENTIRE second nest (the
// ppp / p4 recurrence, roughly half the program) was never executed by the
// suite at all.  This reference covers both paths.
//
// Plain scalar C over 1-based arrays, mirroring the Sisal index-for-index, so
// it can double as a performance baseline later.
//
// SIZING.  The largest index written is
//     first nest : ir + 2 + irmax2
//     second nest: irmax2*ir + ir + 2
// so jxxmx must be at least the latter whenever ir > 2.  With the suite's
// historical irmax2 = 4, jxxmx = 16, an ir of 3 would write index 17 and run
// off the end -- there is no runtime subscript checking, so it would corrupt
// silently.  ref_legpoly_min_size() states the requirement and the harness
// asserts it rather than trusting the caller.

#include <cmath>
#include <vector>

namespace legpolyref {

static inline int min_size (int ir, int irmax2)
{
  const int a = ir + 2 + irmax2;
  const int b = irmax2 * ir + ir + 2;
  return (ir == 2) ? a : (a > b ? a : b);
}

// Result is 1-based: out[1..jxxmx].  out[0] is unused padding.
static inline std::vector<double> ref_legpoly (int ir, int irmax2, int jxxmx,
                                               float coas, float sias,
                                               float deltas)
{
  const double coa = (double)coas, sia = (double)sias, delta = (double)deltas;
  const int irpp = ir + 2;
  const double theta = delta, sqr2 = sqrt (2.0);

  std::vector<double> p ((size_t)jxxmx + 1, 0.0);
  p[1] = 1.0 / sqr2;

  // ---- first nest: the trigonometric series ----
  double c1 = sqr2;
  for (int n = 1; n <= irpp; n++)
    {
      const double fn = (double)n, fn2 = 2.0 * fn, fn2sq = fn2 * fn2;
      c1 = c1 * sqrt (1.0 - 1.0 / fn2sq);
      const double c3 = c1 / sqrt (fn * (fn + 1.0));

      double ang = fn * theta, ss1 = 0.0, ss2 = 0.0;
      double c4 = 1.0, c5 = fn, a = -1.0, b = 0.0;
      const int n1 = n + 1;
      for (int kk = 1; kk <= n1;)
        {
          const int oldkk = kk;
          kk = oldkk + 2;
          const int k = oldkk - 1;
          ss2 = ss2 + c5 * sin (ang) * c4;
          // the HALF weight lands on the k == n term only
          const double c4t = (k == n) ? 0.5 * c4 : c4;
          ss1 = ss1 + c4t * cos (ang);
          a = a + 2.0;
          b = b + 1.0;
          const double fk = (double)k;
          const double nang = theta * (fn - fk - 2.0);
          c4 = (a * (fn - b + 1.0) / (b * (fn2 - a))) * c4t;
          c5 = c5 - 2.0;
          ang = nang;
        }
      if (n - irpp < 0) { p[n + 1] = ss1 * c1; p[n + irmax2] = ss2 * c3; }
      else if (n - irpp == 0) { p[n + irmax2] = ss2 * c3; }
    }

  if (ir == 2) return p;   // the short-circuit the old test always took

  // ---- second nest: the ppp / p4 three-term recurrence ----
  for (int m = 2; m <= ir; m++)
    {
      const double fm = (double)m;
      const double fm1 = fm - 1.0, fm2 = fm - 2.0, fm3 = fm - 3.0;
      const int mm1 = m - 1, m1 = m + 1;
      const double c6 = sqrt ((2.0 * fm + 1.0) / (2.0 * fm));
      p[irmax2 * m + 1] = c6 * sia * p[irmax2 * mm1 + 1];
      const int mpir = m + ir + 1, mt = m;
      for (int l = m1; l <= mpir; l++)
        {
          const double fn = (double)l;
          const double c7 = (fn * 2.0 + 1.0) / (fn * 2.0 - 1.0);
          const double c8 = (fm1 + fn) / ((fm + fn) * (fm2 + fn));
          const double c
              = sqrt ((fn * 2.0 + 1.0) / (fn * 2.0 - 3.0) * c8 * (fm3 + fn));
          const double d = sqrt (c7 * c8 * (fn - fm1));
          const double e = sqrt (c7 * (fn - fm) / (fn + fm));
          const int lm = irmax2 * mt + l - mt + 1;
          const int lmm2 = irmax2 * (mt - 2) + l - mt + 3;
          const int lm1mm2 = lmm2 - 1, lm2mm2 = lm1mm2 - 1, lm1m = lm - 1;
          if (l - mpir < 0)
            p[lm] = c * p[lm2mm2] - d * p[lm1mm2] * coa + e * p[lm1m] * coa;
          else if (l - mpir == 0)
            {
              const double a
                  = sqrt ((fn * fn - 0.25) / (fn * fn - fm * fm));
              const double b
                  = sqrt ((2.0 * fn + 1.0) * (fn - fm - 1.0) * (fn + fm1)
                          / ((2.0 * fn - 3.0) * (fn - fm) * (fn + fm)));
              const int lm2m = lm1m - 1;
              p[lm] = 2.0 * a * coa * p[lm1m] - b * p[lm2m];
            }
          // l - mpir > 0 leaves p untouched
        }
    }
  return p;
}

}  // namespace legpolyref
#endif
