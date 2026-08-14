#ifndef HILBERT_REF_H
#define HILBERT_REF_H
// C reference for the hilbert_dv residual test (test/e2e/hilbert_dv.sis).
//
// The .sis returns only ||H x - b||, not x, so the solution cannot be compared
// directly.  What the reference buys instead is a FAIR BAR: a plain LU solve
// with partial pivoting on the same data, whose residual says what a correct
// solver actually achieves there.  The old test asserted `resid < 1e-12` at
// n = 4 and nothing else -- a bar that is both arbitrary (it happens to hold
// for n = 4 and fails for larger Hilbert systems purely from conditioning) and
// blind to the -999 singular branch, which nothing exercised.
//
// Plain scalar C, reusable as a performance baseline later.

#include <cmath>
#include <vector>

namespace hilbref {

// Solve A x = b by LU with partial pivoting.  A is n*n row-major, 1 copy taken.
// Returns false if the matrix is numerically singular (no usable pivot).
static inline bool lu_solve (int n, const std::vector<double> &A_in,
                             const std::vector<double> &b_in,
                             std::vector<double> &x)
{
  std::vector<double> A = A_in;
  x = b_in;
  std::vector<int> piv (n);
  for (int i = 0; i < n; i++) piv[i] = i;
  for (int k = 0; k < n; k++)
    {
      int p = k;
      for (int i = k + 1; i < n; i++)
        if (fabs (A[i * n + k]) > fabs (A[p * n + k])) p = i;
      if (fabs (A[p * n + k]) < 1e-300) return false;
      if (p != k)
        {
          for (int j = 0; j < n; j++) std::swap (A[k * n + j], A[p * n + j]);
          std::swap (x[k], x[p]);
        }
      for (int i = k + 1; i < n; i++)
        {
          const double f = A[i * n + k] / A[k * n + k];
          A[i * n + k] = f;
          for (int j = k + 1; j < n; j++) A[i * n + j] -= f * A[k * n + j];
          x[i] -= f * x[k];
        }
    }
  for (int i = n - 1; i >= 0; i--)
    {
      for (int j = i + 1; j < n; j++) x[i] -= A[i * n + j] * x[j];
      x[i] /= A[i * n + i];
    }
  return true;
}

// ||A x - b||_2 for the x the reference solver produces.  Negative if singular.
static inline double ref_resid (int n, const std::vector<double> &A,
                                const std::vector<double> &b)
{
  std::vector<double> x;
  if (!lu_solve (n, A, b, x)) return -1.0;
  double s = 0.0;
  for (int i = 0; i < n; i++)
    {
      double r = 0.0;
      for (int j = 0; j < n; j++) r += A[i * n + j] * x[j];
      r -= b[i];
      s += r * r;
    }
  return sqrt (s);
}

}  // namespace hilbref
#endif
