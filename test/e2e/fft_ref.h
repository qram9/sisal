#ifndef FFT_REF_H
#define FFT_REF_H
// Direct O(n^2) DFT -- the reference for feo_fft / feo_fft_dv.
//
// An FFT is one of the few things with a perfect, obviously-correct reference,
// so there is no excuse for a size-only check here.  The suite previously
// asserted only `size == 4` on the full radix-4 FFT, at the single input
// n = 4 -- which is the largest size that happens to work.  Checking the values
// against this reference showed n >= 16 is wrong (see the harness).
//
// The same shape of blind spot already bit this program once: per the project
// notes, feo_fft_parts3's size-only check hid garbage values until a value
// oracle was applied.

#include <cmath>
#include <vector>

namespace fftref {

// The input feo_fft's data(n) builds: x[i] = cos(2*pi*i/n), imaginary part 0.
static inline void ref_input (int n, std::vector<double> &xr,
                              std::vector<double> &xi)
{
  xr.assign (n, 0.0);
  xi.assign (n, 0.0);
  const double tt = 8.0 * atan (1.0) / (double)n;
  for (int i = 0; i < n; i++) xr[i] = cos (tt * (double)i);
}

static inline void ref_dft (const std::vector<double> &xr,
                            const std::vector<double> &xi,
                            std::vector<double> &yr, std::vector<double> &yi)
{
  const int n = (int)xr.size ();
  yr.assign (n, 0.0);
  yi.assign (n, 0.0);
  for (int k = 0; k < n; k++)
    for (int j = 0; j < n; j++)
      {
        const double a = -2.0 * M_PI * (double)k * (double)j / (double)n;
        yr[k] += xr[j] * cos (a) - xi[j] * sin (a);
        yi[k] += xr[j] * sin (a) + xi[j] * cos (a);
      }
}

// max |got - dft| over both components; -1 if the size is wrong
static inline double ref_max_err (int n, const double *gr, const double *gi,
                                  int got_n)
{
  if (got_n != n) return -1.0;
  std::vector<double> xr, xi, yr, yi;
  ref_input (n, xr, xi);
  ref_dft (xr, xi, yr, yi);
  double worst = 0.0;
  for (int k = 0; k < n; k++)
    {
      const double d = fabs (gr[k] - yr[k]) + fabs (gi[k] - yi[k]);
      if (d > worst) worst = d;
    }
  return worst;
}

}  // namespace fftref
#endif
