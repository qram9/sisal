// unsplit_ref.h -- a reference implementation of one unsplit timestep, in C++.
//
// Written from test/unit/unsplit.sis, independently of the Sisal-to-C++ path,
// so that unsplit_dv (part 8) is checked against COMPUTED VALUES and not only
// against conservation / uniform-flow / symmetry properties.  The per-stage
// groups (parts 1..7) each verify their own stage in isolation; what this adds
// is the WIRING -- which stage feeds which, in what argument order -- and that
// is precisely what per-stage references cannot see.
//
// Index ranges follow the source exactly and differ per stage; each is stated
// where it is built.  ilo = 1 throughout, as part 8's main passes it.
#pragma once
#include <algorithm>
#include <cmath>
#include <vector>

namespace uref {

static const int NCX = 4;

// a 2-D array with explicit inclusive bounds, so each stage can carry the
// source's own range instead of a shifted one
struct A2 {
  int j0, j1, i0, i1, W;
  std::vector<double> a;
  A2 (int J0, int J1, int I0, int I1, double f = 0.0)
      : j0 (J0), j1 (J1), i0 (I0), i1 (I1), W (I1 - I0 + 1),
        a ((size_t)(J1 - J0 + 1) * (I1 - I0 + 1), f) {}
  double &at (int j, int i) { return a[(size_t)(j - j0) * W + (i - i0)]; }
  double at (int j, int i) const { return a[(size_t)(j - j0) * W + (i - i0)]; }
};

static inline double fsign (double x, double y) { return y >= 0.0 ? std::fabs (x) : -std::fabs (x); }
static inline double sqr (double x) { return x * x; }

// ---- PhysBnd: wrap (periodic) or clamp, ncx cells on every side -----------
static A2 physbnd (const A2 &in, int nx, int ny, bool xper, bool yper)
{
  A2 w (1 - NCX, ny + NCX, 1 - NCX, nx + NCX);
  for (int j = w.j0; j <= w.j1; j++)
    for (int i = w.i0; i <= w.i1; i++)
      {
        int jj = (j <= 0) ? (yper ? ny + j : 1) : (j > ny) ? (yper ? j - ny : ny) : j;
        int ii = (i <= 0) ? (xper ? nx + i : 1) : (i > nx) ? (xper ? i - nx : nx) : i;
        w.at (j, i) = in.at (jj, ii);
      }
  return w;
}

// ---- Method1: conserved -> primitive --------------------------------------
struct Prim { A2 rho, u, v, e; };
static Prim method1 (const A2 &U1, const A2 &U2, const A2 &U3, const A2 &U4,
                     int nc1, int nc2)
{
  Prim p { A2 (1 - NCX, nc2 + NCX, 1 - NCX, nc1 + NCX),
           A2 (1 - NCX, nc2 + NCX, 1 - NCX, nc1 + NCX),
           A2 (1 - NCX, nc2 + NCX, 1 - NCX, nc1 + NCX),
           A2 (1 - NCX, nc2 + NCX, 1 - NCX, nc1 + NCX) };
  for (int j = p.rho.j0; j <= p.rho.j1; j++)
    for (int i = p.rho.i0; i <= p.rho.i1; i++)
      {
        double r = U1.at (j, i);
        p.rho.at (j, i) = r;
        p.u.at (j, i) = U2.at (j, i) / r;
        p.v.at (j, i) = U3.at (j, i) / r;
        p.e.at (j, i) = U4.at (j, i) / r;
      }
  return p;
}

// ---- Method2: equation of state, with the pressure floor ------------------
static void method2 (const Prim &q, int nc1, int nc2, double small, double gm1,
                     A2 &psml, A2 &p)
{
  for (int j = psml.j0; j <= psml.j1; j++)
    for (int i = psml.i0; i <= psml.i1; i++)
      {
        double eken = 0.5 * (sqr (q.u.at (j, i)) + sqr (q.v.at (j, i)));
        double eint = q.e.at (j, i) - eken;
        psml.at (j, i) = small * q.rho.at (j, i) * eken;
        p.at (j, i) = std::max (small * q.rho.at (j, i) * eken,
                                gm1 * q.rho.at (j, i) * eint);
      }
}

// ---- Method3: sound speed, on 0..nc+1 -------------------------------------
static A2 method3 (double gamma, const A2 &p, const A2 &rho, int nc1, int nc2)
{
  A2 c (0, nc2 + 1, 0, nc1 + 1);
  for (int j = 0; j <= nc2 + 1; j++)
    for (int i = 0; i <= nc1 + 1; i++)
      c.at (j, i) = std::sqrt (gamma * p.at (j, i) / rho.at (j, i));
  return c;
}

// ---- flaten: the shock-flattening coefficient, on 0..nc+1 -----------------
static A2 flaten (const A2 &p, const A2 &u, const A2 &v, int nc1, int nc2,
                  int godorder)
{
  const double small = 1e-6, shk = 0.33, zc1 = 0.75, dz = 1.0 / (0.85 - 0.75);
  A2 out (0, nc2 + 1, 0, nc1 + 1, 0.0);
  if (godorder != 2) return out;
  auto chi = [&] (double dp, double den, double lo, bool comp) {
    double zeta = std::fabs (dp) / std::max (small, den);
    double z = std::min (1.0, std::max (0.0, dz * (zeta - zc1)));
    double c = ((std::fabs (dp) / lo) > shk) ? (comp ? 1.0 : 0.0) : 0.0;
    return c * z;
  };
  for (int j = 0; j <= nc2 + 1; j++)
    for (int i = 0; i <= nc1 + 1; i++)
      {
        double mx = 0;
        for (int k = i - 1; k <= i + 1; k++)
          mx = std::max (mx, chi (p.at (j, k + 1) - p.at (j, k - 1),
                                  std::fabs (p.at (j, k + 2) - p.at (j, k - 2)),
                                  std::min (p.at (j, k + 1), p.at (j, k - 1)),
                                  u.at (j, k - 1) >= u.at (j, k + 1)));
        double my = 0;
        for (int k = j - 1; k <= j + 1; k++)
          my = std::max (my, chi (p.at (k + 1, i) - p.at (k - 1, i),
                                  std::fabs (p.at (k + 2, i) - p.at (k - 2, i)),
                                  std::min (p.at (k + 1, i), p.at (k - 1, i)),
                                  v.at (k - 1, i) >= v.at (k + 1, i)));
        out.at (j, i) = std::min (1.0 - mx, 1.0 - my);
      }
  return out;
}

// ---- slope: limited Fromm slopes, both directions, on 0..nc+1 -------------
struct Slopes { A2 x, y; };
static Slopes slope (const A2 &q, const A2 &flatn, int nc1, int nc2)
{
  const double t3c = 2.0 / 3.0, s6 = 1.0 / 6.0;
  Slopes s { A2 (0, nc2 + 1, 0, nc1 + 1), A2 (0, nc2 + 1, 0, nc1 + 1) };
  // x direction
  for (int j = 0; j <= nc2 + 1; j++)
    {
      A2 df (0, 0, -1, nc1 + 2), ds (0, 0, -1, nc1 + 2), dl (0, 0, -1, nc1 + 2);
      for (int i = -1; i <= nc1 + 2; i++)
        {
          double dcen = 0.5 * (q.at (j, i + 1) - q.at (j, i - 1));
          double dlft = 2.0 * (q.at (j, i) - q.at (j, i - 1));
          double drgt = 2.0 * (q.at (j, i + 1) - q.at (j, i));
          double slop = std::min (std::fabs (dlft),
                                  std::min (std::fabs (drgt), std::fabs (dcen)));
          double lim = (dlft * drgt >= 0.0) ? slop : 0.0;
          ds.at (0, i) = fsign (1.0, dcen);
          dl.at (0, i) = lim;
          df.at (0, i) = fsign (1.0, dcen) * lim;
        }
      for (int i = 0; i <= nc1 + 1; i++)
        {
          double d3 = t3c * (q.at (j, i + 1) - q.at (j, i - 1))
                      - s6 * (df.at (0, i + 1) - df.at (0, i - 1));
          s.x.at (j, i) = flatn.at (j, i) * ds.at (0, i)
                          * std::min (dl.at (0, i), std::fabs (d3));
        }
    }
  // y direction
  A2 Xdf (-1, nc2 + 2, 0, nc1 + 1), Xds (-1, nc2 + 2, 0, nc1 + 1),
      Xdl (-1, nc2 + 2, 0, nc1 + 1);
  for (int j = -1; j <= nc2 + 2; j++)
    for (int i = 0; i <= nc1 + 1; i++)
      {
        double dcen = 0.5 * (q.at (j + 1, i) - q.at (j - 1, i));
        double dlft = 2.0 * (q.at (j, i) - q.at (j - 1, i));
        double drgt = 2.0 * (q.at (j + 1, i) - q.at (j, i));
        double slop = std::min (std::fabs (dlft),
                                std::min (std::fabs (drgt), std::fabs (dcen)));
        double lim = (dlft * drgt >= 0.0) ? slop : 0.0;
        Xds.at (j, i) = fsign (1.0, dcen);
        Xdl.at (j, i) = lim;
        Xdf.at (j, i) = fsign (1.0, dcen) * lim;
      }
  for (int j = 0; j <= nc2 + 1; j++)
    for (int i = 0; i <= nc1 + 1; i++)
      {
        double d4 = t3c * (q.at (j + 1, i) - q.at (j - 1, i))
                    - s6 * (Xdf.at (j + 1, i) - Xdf.at (j - 1, i));
        s.y.at (j, i) = flatn.at (j, i) * Xds.at (j, i)
                        * std::min (Xdl.at (j, i), std::fabs (d4));
      }
  return s;
}

// ---- fluxev: the Riemann solver, over an index range ----------------------
static void fluxev (const std::vector<double> &rl, const std::vector<double> &ul,
                    const std::vector<double> &vl, const std::vector<double> &pl,
                    const std::vector<double> &rr, const std::vector<double> &ur,
                    const std::vector<double> &vr, const std::vector<double> &pr,
                    const std::vector<double> &smallp, int niter, double gamma,
                    double xi, std::vector<double> f[4])
{
  const double half = 0.5, forth = 0.25, small = 1e-6;
  const double gm1 = gamma - 1.0, gp1 = gamma + 1.0;
  const size_t n = rl.size ();
  for (int q = 0; q < 4; q++) f[q].assign (n, 0.0);
  for (size_t k = 0; k < n; k++)
    {
      double ps = (std::sqrt (gamma * rr[k] * pr[k]) * pl[k]
                   + std::sqrt (gamma * rl[k] * pl[k]) * pr[k]
                   + std::sqrt (gamma * rl[k] * pl[k])
                         * std::sqrt (gamma * rr[k] * pr[k]) * (ul[k] - ur[k]))
                  / (std::sqrt (gamma * rl[k] * pl[k])
                     + std::sqrt (gamma * rr[k] * pr[k]));
      ps = std::max (smallp[k], ps);
      for (int it = 1; it <= niter; it++)
        {
          double wl = std::sqrt (half * rl[k] * (gp1 * ps + gm1 * pl[k]));
          double wlf = 1.0 / wl, dwl = forth * rl[k] * gp1 * wlf;
          double usl = ul[k] - wlf * (ps - pl[k]);
          double dusl = wlf * (wlf * dwl * (ps - pl[k]) - 1.0);
          double wr = std::sqrt (half * rr[k] * (gp1 * ps + gm1 * pr[k]));
          double wrf = 1.0 / wr, dwr = forth * rr[k] * gp1 * wrf;
          double usr = ur[k] + wrf * (ps - pr[k]);
          double dusr = wrf * (1.0 - wrf * dwr * (ps - pr[k]));
          ps = std::max (smallp[k], ps - (usl - usr) / (dusl - dusr));
        }
      double wlsq = half * rl[k] * (gp1 * ps + gm1 * pl[k]);
      double wrsq = half * rr[k] * (gp1 * ps + gm1 * pr[k]);
      double ustar = half * ((ul[k] + (ps - pl[k]) / -std::sqrt (wlsq))
                             + (ur[k] + (ps - pr[k]) / std::sqrt (wrsq)));
      double rstarl = wlsq * rl[k] / (wlsq - rl[k] * (ps - pl[k]));
      double rstarr = wrsq * rr[k] / (wrsq - rr[k] * (ps - pr[k]));
      double chi = fsign (1.0, xi - ustar);
      double ro, uo, vo, po, ri, vi;
      if (chi >= 0.0) { ro = rr[k]; uo = ur[k]; vo = vr[k]; po = pr[k]; ri = rstarr; vi = vr[k]; }
      else            { ro = rl[k]; uo = ul[k]; vo = vl[k]; po = pl[k]; ri = rstarl; vi = vl[k]; }
      double ui = ustar, pi = ps;
      double ci = std::sqrt (gamma * pi / ri), co = std::sqrt (gamma * po / ro);
      double wo = std::sqrt (half * ro * (gp1 * pi + gm1 * po));
      double shock = chi * uo + wo / ro, si, so;
      if (pi - po < 0.0) { si = chi * ui + ci; so = chi * uo + co; }
      else               { si = so = shock; }
      double sden = 1.0 / std::max (small, so - si);
      double frac1 = (chi * xi >= so) ? 0.0 : (so - xi * chi) * sden;
      double frac = (chi * xi < si) ? 1.0 : frac1;
      double rg = ro + frac * (ri - ro), ug = uo + frac * (ui - uo);
      double vg = vo + frac * (vi - vo), pg = po + frac * (pi - po);
      f[0][k] = rg * ug;
      f[1][k] = rg * sqr (ug) + pg;
      f[2][k] = rg * ug * vg;
      f[3][k] = ug * (gamma * pg / gm1 + half * rg * (sqr (ug) + sqr (vg)));
    }
}


// ---- Method5..8: the traced states ---------------------------------------
struct Face { A2 r, u, v, p; };
// x faces: jc in 0..nc2+1, ie in 1..nc1+1 ; y faces: je in 1..nc2+1, ic in 0..nc1+1
static Face method5 (const A2 &c, const A2 &u1, const A2 &rho, const A2 &v1,
                     const A2 &p, const A2 &psml, const Slopes &drho,
                     const Slopes &dp, const Slopes &du, const Slopes &dv,
                     int nc1, int nc2, double dtdx, double hdtdx, double smallr)
{
  Face f { A2 (0, nc2 + 1, 1, nc1 + 1), A2 (0, nc2 + 1, 1, nc1 + 1),
           A2 (0, nc2 + 1, 1, nc1 + 1), A2 (0, nc2 + 1, 1, nc1 + 1) };
  for (int jc = 0; jc <= nc2 + 1; jc++)
    for (int ie = 1; ie <= nc1 + 1; ie++)
      {
        int ic = ie - 1;
        double cc = c.at (jc, ic), uu = u1.at (jc, ic);
        double alpha = 0.5 * (1.0 - dtdx * std::max (0.0, uu + cc));
        double t2 = cc * drho.x.at (jc, ic) - dp.x.at (jc, ic) / cc;
        double beta0 = (uu >= 0.0) ? t2 : 0.0;
        double t3 = 2.0 * (dp.x.at (jc, ic) / rho.at (jc, ic) - cc * du.x.at (jc, ic));
        double betam = (uu - cc >= 0.0) ? t3 : 0.0;
        double beta = (uu >= 0.0) ? cc * dv.x.at (jc, ic) : 0.0;
        f.r.at (jc, ie) = std::max (smallr,
            rho.at (jc, ic) + alpha * drho.x.at (jc, ic)
            + hdtdx * (beta0 + 0.5 * rho.at (jc, ic) * betam / cc));
        f.u.at (jc, ie) = u1.at (jc, ic) + alpha * du.x.at (jc, ic) - hdtdx * 0.5 * betam;
        f.v.at (jc, ie) = v1.at (jc, ic) + alpha * dv.x.at (jc, ic) + hdtdx * beta;
        double p2 = p.at (jc, ic) + alpha * dp.x.at (jc, ic)
                    + hdtdx * 0.5 * rho.at (jc, ic) * cc * betam;
        f.p.at (jc, ie) = std::max (psml.at (jc, ic), std::max (psml.at (jc, ic + 1), p2));
      }
  return f;
}
static Face method6 (const A2 &c, const A2 &u1, const A2 &rho, const A2 &v1,
                     const A2 &p, const A2 &psml, const Slopes &drho,
                     const Slopes &dp, const Slopes &du, const Slopes &dv,
                     int nc1, int nc2, double dtdx, double hdtdx, double smallr)
{
  Face f { A2 (0, nc2 + 1, 1, nc1 + 1), A2 (0, nc2 + 1, 1, nc1 + 1),
           A2 (0, nc2 + 1, 1, nc1 + 1), A2 (0, nc2 + 1, 1, nc1 + 1) };
  for (int jc = 0; jc <= nc2 + 1; jc++)
    for (int ie = 1; ie <= nc1 + 1; ie++)
      {
        int ic = ie;
        double cc = c.at (jc, ic), uu = u1.at (jc, ic);
        double alpha = 0.5 * (1.0 + dtdx * std::min (0.0, uu - cc));
        double t2 = dp.x.at (jc, ic) / cc - cc * drho.x.at (jc, ic);
        double beta0 = (uu < 0.0) ? t2 : 0.0;
        double t3 = -2.0 * (cc * du.x.at (jc, ic) + dp.x.at (jc, ic) / rho.at (jc, ic));
        double betap = (uu + cc < 0.0) ? t3 : 0.0;
        double beta = (uu < 0.0) ? -cc * dv.x.at (jc, ic) : 0.0;
        f.r.at (jc, ie) = std::max (smallr,
            rho.at (jc, ic) - alpha * drho.x.at (jc, ic)
            + hdtdx * (beta0 + 0.5 * rho.at (jc, ic) * betap / cc));
        f.u.at (jc, ie) = u1.at (jc, ic) - alpha * du.x.at (jc, ic) + hdtdx * 0.5 * betap;
        f.v.at (jc, ie) = v1.at (jc, ic) - alpha * dv.x.at (jc, ic) + hdtdx * beta;
        double p2 = p.at (jc, ic) - alpha * dp.x.at (jc, ic)
                    + hdtdx * 0.5 * rho.at (jc, ic) * cc * betap;
        f.p.at (jc, ie) = std::max (psml.at (jc, ic - 1), std::max (psml.at (jc, ic), p2));
      }
  return f;
}
static Face method7 (const A2 &c, const A2 &v1, const A2 &u1, const A2 &rho,
                     const A2 &p, const A2 &psml, const Slopes &drho,
                     const Slopes &dp, const Slopes &du, const Slopes &dv,
                     int nc1, int nc2, double dtdy, double hdtdy, double smallr)
{
  Face f { A2 (1, nc2 + 1, 0, nc1 + 1), A2 (1, nc2 + 1, 0, nc1 + 1),
           A2 (1, nc2 + 1, 0, nc1 + 1), A2 (1, nc2 + 1, 0, nc1 + 1) };
  for (int je = 1; je <= nc2 + 1; je++)
    for (int ic = 0; ic <= nc1 + 1; ic++)
      {
        int jc = je - 1;
        double cc = c.at (jc, ic), vv = v1.at (jc, ic);
        double alpha = 0.5 * (1.0 - dtdy * std::max (vv + cc, 0.0));
        double t1 = cc * drho.y.at (jc, ic) - dp.y.at (jc, ic) / cc;
        double beta0 = (vv >= 0.0) ? t1 : 0.0;
        double beta = (vv >= 0.0) ? cc * du.y.at (jc, ic) : 0.0;
        double t2 = 2.0 * (dp.y.at (jc, ic) / rho.at (jc, ic) - cc * dv.y.at (jc, ic));
        double betam = (vv - cc >= 0.0) ? t2 : 0.0;
        f.r.at (je, ic) = std::max (smallr,
            rho.at (jc, ic) + alpha * drho.y.at (jc, ic)
            + hdtdy * (beta0 + 0.5 * rho.at (jc, ic) * betam / cc));
        f.u.at (je, ic) = u1.at (jc, ic) + alpha * du.y.at (jc, ic) + hdtdy * beta;
        f.v.at (je, ic) = v1.at (jc, ic) + alpha * dv.y.at (jc, ic) - hdtdy * 0.5 * betam;
        double p2 = p.at (jc, ic) + alpha * dp.y.at (jc, ic)
                    + hdtdy * 0.5 * cc * rho.at (jc, ic) * betam;
        f.p.at (je, ic) = std::max (psml.at (jc, ic), std::max (psml.at (jc + 1, ic), p2));
      }
  return f;
}
static Face method8 (const A2 &c, const A2 &v1, const A2 &u1, const A2 &rho,
                     const A2 &p, const A2 &psml, const Slopes &drho,
                     const Slopes &dp, const Slopes &du, const Slopes &dv,
                     int nc1, int nc2, double dtdy, double hdtdy, double smallr)
{
  Face f { A2 (1, nc2 + 1, 0, nc1 + 1), A2 (1, nc2 + 1, 0, nc1 + 1),
           A2 (1, nc2 + 1, 0, nc1 + 1), A2 (1, nc2 + 1, 0, nc1 + 1) };
  for (int je = 1; je <= nc2 + 1; je++)
    for (int ic = 0; ic <= nc1 + 1; ic++)
      {
        int jc = je;
        double cc = c.at (jc, ic), vv = v1.at (jc, ic);
        double alpha = 0.5 * (1.0 + dtdy * std::min (vv - cc, 0.0));
        double t1 = dp.y.at (jc, ic) / cc - cc * drho.y.at (jc, ic);
        double beta0 = (vv < 0.0) ? t1 : 0.0;
        double beta = (vv < 0.0) ? -cc * du.y.at (jc, ic) : 0.0;
        double t2 = -2.0 * (dp.y.at (jc, ic) / rho.at (jc, ic) + cc * dv.y.at (jc, ic));
        double betap = (vv + cc < 0.0) ? t2 : 0.0;
        f.r.at (je, ic) = std::max (smallr,
            rho.at (jc, ic) - alpha * drho.y.at (jc, ic)
            + hdtdy * (beta0 + 0.5 * rho.at (jc, ic) * betap / cc));
        f.u.at (je, ic) = u1.at (jc, ic) - alpha * du.y.at (jc, ic) + hdtdy * beta;
        f.v.at (je, ic) = v1.at (jc, ic) - alpha * dv.y.at (jc, ic) + hdtdy * 0.5 * betap;
        double p2 = p.at (jc, ic) - alpha * dp.y.at (jc, ic)
                    + hdtdy * 0.5 * cc * rho.at (jc, ic) * betap;
        f.p.at (je, ic) = std::max (psml.at (jc, ic), std::max (psml.at (jc - 1, ic), p2));
      }
  return f;
}

// ---- Method9/10: transverse fluxes (row-wise Riemann solves) --------------
struct Flux4 { A2 f1, f2, f3, f4; };
// Method9: for je in 1..nc2+1, solve along ic in 0..nc1+1 with v as the NORMAL
// velocity; returns f1, F3, F2, f4 -- the momentum fluxes SWAPPED, so the
// caller sees them in (x, y) order.
static Flux4 method9 (const Face &b, const Face &t, const A2 &psml, int nc1,
                      int nc2, int niter, double gamma, double xi)
{
  Flux4 out { A2 (1, nc2 + 1, 0, nc1 + 1), A2 (1, nc2 + 1, 0, nc1 + 1),
              A2 (1, nc2 + 1, 0, nc1 + 1), A2 (1, nc2 + 1, 0, nc1 + 1) };
  const int n = nc1 + 2;
  for (int je = 1; je <= nc2 + 1; je++)
    {
      std::vector<double> rl (n), ul (n), vl (n), pl (n), rr (n), ur (n),
          vr (n), pr (n), sm (n), f[4];
      for (int ic = 0; ic <= nc1 + 1; ic++)
        {
          int k = ic;
          rl[k] = b.r.at (je, ic); ul[k] = b.v.at (je, ic);
          vl[k] = b.u.at (je, ic); pl[k] = b.p.at (je, ic);
          rr[k] = t.r.at (je, ic); ur[k] = t.v.at (je, ic);
          vr[k] = t.u.at (je, ic); pr[k] = t.p.at (je, ic);
          sm[k] = std::max (psml.at (je - 1, ic), psml.at (je, ic));
        }
      fluxev (rl, ul, vl, pl, rr, ur, vr, pr, sm, niter, gamma, xi, f);
      for (int ic = 0; ic <= nc1 + 1; ic++)
        {
          out.f1.at (je, ic) = f[0][ic];
          out.f2.at (je, ic) = f[2][ic];      // f3
          out.f3.at (je, ic) = f[1][ic];      // f2
          out.f4.at (je, ic) = f[3][ic];
        }
    }
  return out;
}
// Method10: for jc in 0..nc2+1, solve along ie in 1..nc1+1; NO swap.
static Flux4 method10 (const Face &l, const Face &r, const A2 &psml, int nc1,
                       int nc2, int niter, double gamma, double xi)
{
  Flux4 out { A2 (0, nc2 + 1, 1, nc1 + 1), A2 (0, nc2 + 1, 1, nc1 + 1),
              A2 (0, nc2 + 1, 1, nc1 + 1), A2 (0, nc2 + 1, 1, nc1 + 1) };
  const int n = nc1 + 1;
  for (int jc = 0; jc <= nc2 + 1; jc++)
    {
      std::vector<double> rl (n), ul (n), vl (n), pl (n), rr (n), ur (n),
          vr (n), pr (n), sm (n), f[4];
      for (int ie = 1; ie <= nc1 + 1; ie++)
        {
          int k = ie - 1;
          rl[k] = l.r.at (jc, ie); ul[k] = l.u.at (jc, ie);
          vl[k] = l.v.at (jc, ie); pl[k] = l.p.at (jc, ie);
          rr[k] = r.r.at (jc, ie); ur[k] = r.u.at (jc, ie);
          vr[k] = r.v.at (jc, ie); pr[k] = r.p.at (jc, ie);
          sm[k] = std::max (psml.at (jc, ie), psml.at (jc, ie - 1));
        }
      fluxev (rl, ul, vl, pl, rr, ur, vr, pr, sm, niter, gamma, xi, f);
      for (int ie = 1; ie <= nc1 + 1; ie++)
        {
          out.f1.at (jc, ie) = f[0][ie - 1];
          out.f2.at (jc, ie) = f[1][ie - 1];
          out.f3.at (jc, ie) = f[2][ie - 1];
          out.f4.at (jc, ie) = f[3][ie - 1];
        }
    }
  return out;
}

// ---- Method11..14: the transverse predictor ------------------------------
// Convert to conservation form, subtract the transverse flux difference,
// convert back.  Written out rather than shared, because the four differ in
// which axis they difference, which cell they read, AND -- for 13/14 -- in
// which index is the OUTER one, so their results are stored [ic][je].
static void conv_back (double rn, double un, double vn, double en,
                       double smallr, double gm1, double small, double &r,
                       double &u, double &v, double &p)
{
  double r3 = std::max (smallr, rn);
  double eken = 0.5 * (sqr (un) + sqr (vn)) / r3;
  r = r3; u = un / r3; v = vn / r3;
  p = std::max (small * eken, gm1 * (en - eken));
}
// 11: left states, 12: right states.  jc in 1..nc2, ie in 1..nc1+1.
static Face method11_12 (const Face &in, const Flux4 &f2, int nc1, int nc2,
                         double hdtdy, double smallr, double gm1, double small,
                         bool right)
{
  Face o { A2 (1, nc2, 1, nc1 + 1), A2 (1, nc2, 1, nc1 + 1),
           A2 (1, nc2, 1, nc1 + 1), A2 (1, nc2, 1, nc1 + 1) };
  for (int jc = 1; jc <= nc2; jc++)
    for (int ie = 1; ie <= nc1 + 1; ie++)
      {
        int ic = right ? ie : ie - 1;
        double rr = in.r.at (jc, ie);
        double ru = rr * in.u.at (jc, ie), rv = rr * in.v.at (jc, ie);
        double re = in.p.at (jc, ie) / gm1
                    + 0.5 * rr * (sqr (in.u.at (jc, ie)) + sqr (in.v.at (jc, ie)));
        double rn = rr - hdtdy * (f2.f1.at (jc + 1, ic) - f2.f1.at (jc, ic));
        double un = ru - hdtdy * (f2.f2.at (jc + 1, ic) - f2.f2.at (jc, ic));
        double vn = rv - hdtdy * (f2.f3.at (jc + 1, ic) - f2.f3.at (jc, ic));
        double en = re - hdtdy * (f2.f4.at (jc + 1, ic) - f2.f4.at (jc, ic));
        conv_back (rn, un, vn, en, smallr, gm1, small, o.r.at (jc, ie),
                   o.u.at (jc, ie), o.v.at (jc, ie), o.p.at (jc, ie));
      }
  return o;
}
// 13: bottom states, 14: top.  OUTER index is ic, so results are [ic][je].
static Face method13_14 (const Face &in, const Flux4 &f1, int nc1, int nc2,
                         double hdtdx, double smallr, double gm1, double small,
                         bool top)
{
  Face o { A2 (1, nc1, 1, nc2 + 1), A2 (1, nc1, 1, nc2 + 1),
           A2 (1, nc1, 1, nc2 + 1), A2 (1, nc1, 1, nc2 + 1) };
  for (int ic = 1; ic <= nc1; ic++)
    for (int je = 1; je <= nc2 + 1; je++)
      {
        int jc = top ? je : je - 1;
        double rr = in.r.at (je, ic);
        double ru = rr * in.u.at (je, ic), rv = rr * in.v.at (je, ic);
        double re = in.p.at (je, ic) / gm1
                    + 0.5 * rr * (sqr (in.u.at (je, ic)) + sqr (in.v.at (je, ic)));
        double rn = rr - hdtdx * (f1.f1.at (jc, ic + 1) - f1.f1.at (jc, ic));
        double un = ru - hdtdx * (f1.f2.at (jc, ic + 1) - f1.f2.at (jc, ic));
        double vn = rv - hdtdx * (f1.f3.at (jc, ic + 1) - f1.f3.at (jc, ic));
        double en = re - hdtdx * (f1.f4.at (jc, ic + 1) - f1.f4.at (jc, ic));
        conv_back (rn, un, vn, en, smallr, gm1, small, o.r.at (ic, je),
                   o.u.at (ic, je), o.v.at (ic, je), o.p.at (ic, je));
      }
  return o;
}

// ---- Method15/16: the full fluxes ----------------------------------------
static Flux4 method15 (const Face &l, const Face &r, const A2 &psml, int nc1,
                       int nc2, int niter, double gamma, double xi)
{
  Flux4 out { A2 (1, nc2, 1, nc1 + 1), A2 (1, nc2, 1, nc1 + 1),
              A2 (1, nc2, 1, nc1 + 1), A2 (1, nc2, 1, nc1 + 1) };
  const int n = nc1 + 1;
  for (int jc = 1; jc <= nc2; jc++)
    {
      std::vector<double> rl (n), ul (n), vl (n), pl (n), rr (n), ur (n),
          vr (n), pr (n), sm (n), f[4];
      for (int ie = 1; ie <= nc1 + 1; ie++)
        {
          int k = ie - 1;
          rl[k] = l.r.at (jc, ie); ul[k] = l.u.at (jc, ie);
          vl[k] = l.v.at (jc, ie); pl[k] = l.p.at (jc, ie);
          rr[k] = r.r.at (jc, ie); ur[k] = r.u.at (jc, ie);
          vr[k] = r.v.at (jc, ie); pr[k] = r.p.at (jc, ie);
          sm[k] = std::max (psml.at (jc, ie - 1), psml.at (jc, ie));
        }
      fluxev (rl, ul, vl, pl, rr, ur, vr, pr, sm, niter, gamma, xi, f);
      for (int ie = 1; ie <= nc1 + 1; ie++)
        {
          out.f1.at (jc, ie) = f[0][ie - 1];
          out.f2.at (jc, ie) = f[1][ie - 1];
          out.f3.at (jc, ie) = f[2][ie - 1];
          out.f4.at (jc, ie) = f[3][ie - 1];
        }
    }
  return out;
}
// 16 reads the [ic][je] layout 13/14 produced, and swaps the momentum fluxes
// like Method9; the result is [ic][je] and is transposed afterwards.
static Flux4 method16 (const Face &b, const Face &t, const A2 &psml, int nc1,
                       int nc2, int niter, double gamma, double xi)
{
  Flux4 out { A2 (1, nc1, 1, nc2 + 1), A2 (1, nc1, 1, nc2 + 1),
              A2 (1, nc1, 1, nc2 + 1), A2 (1, nc1, 1, nc2 + 1) };
  const int n = nc2 + 1;
  for (int ic = 1; ic <= nc1; ic++)
    {
      std::vector<double> rl (n), ul (n), vl (n), pl (n), rr (n), ur (n),
          vr (n), pr (n), sm (n), f[4];
      for (int je = 1; je <= nc2 + 1; je++)
        {
          int k = je - 1;
          rl[k] = b.r.at (ic, je); ul[k] = b.v.at (ic, je);
          vl[k] = b.u.at (ic, je); pl[k] = b.p.at (ic, je);
          rr[k] = t.r.at (ic, je); ur[k] = t.v.at (ic, je);
          vr[k] = t.u.at (ic, je); pr[k] = t.p.at (ic, je);
          sm[k] = std::max (psml.at (je, ic), psml.at (je - 1, ic));
        }
      fluxev (rl, ul, vl, pl, rr, ur, vr, pr, sm, niter, gamma, xi, f);
      for (int je = 1; je <= nc2 + 1; je++)
        {
          out.f1.at (ic, je) = f[0][je - 1];
          out.f2.at (ic, je) = f[2][je - 1];   // swapped
          out.f3.at (ic, je) = f[1][je - 1];
          out.f4.at (ic, je) = f[3][je - 1];
        }
    }
  return out;
}

// ---- Transpose, Method17..19, and the composed step ----------------------
static Flux4 transpose4 (const Flux4 &in, int ol, int oh, int il, int ih)
{
  Flux4 o { A2 (ol, oh, il, ih), A2 (ol, oh, il, ih), A2 (ol, oh, il, ih),
            A2 (ol, oh, il, ih) };
  for (int je = ol; je <= oh; je++)
    for (int ic = il; ic <= ih; ic++)
      {
        o.f1.at (je, ic) = in.f1.at (ic, je);
        o.f2.at (je, ic) = in.f2.at (ic, je);
        o.f3.at (je, ic) = in.f3.at (ic, je);
        o.f4.at (je, ic) = in.f4.at (ic, je);
      }
  return o;
}
static A2 method17 (const A2 &u1, const A2 &v1, int nc1, int nc2, double difmag,
                    double dx, double dy)
{
  A2 d (1, nc2 + 1, 1, nc1 + 1);
  for (int je = 1; je <= nc2 + 1; je++)
    for (int ie = 1; ie <= nc1 + 1; ie++)
      {
        double ud = u1.at (je, ie) - u1.at (je, ie - 1) + u1.at (je - 1, ie)
                    - u1.at (je - 1, ie - 1);
        double vd = v1.at (je, ie) - v1.at (je, ie - 1) + v1.at (je - 1, ie)
                    - v1.at (je - 1, ie - 1);
        d.at (je, ie) = difmag * 0.5 * (ud / dx + vd / dy);
      }
  return d;
}
static A2 method18a (const A2 &div, const A2 &flux1, const A2 &Up, int nc1,
                     int nc2, int ilo, double dx)
{
  A2 o (1, nc2, 1, nc1 + 1);
  for (int jc = 1; jc <= nc2; jc++)
    for (int ie = 1; ie <= nc1 + 1; ie++)
      {
        double d1 = std::min (0.0, 0.5 * (div.at (jc, ie) + div.at (jc + 1, ie)));
        o.at (jc, ie) = flux1.at (jc, ie)
                        + dx * d1 * (Up.at (jc, ilo + ie - 1) - Up.at (jc, ilo + ie - 2));
      }
  return o;
}
static A2 method18b (const A2 &div, const A2 &flux2, const A2 &Up, int nc1,
                     int nc2, int ilo, double dy)
{
  A2 o (1, nc2 + 1, 1, nc1);
  for (int je = 1; je <= nc2 + 1; je++)
    for (int ic = 1; ic <= nc1; ic++)
      {
        double d2 = std::min (0.0, 0.5 * (div.at (je, ic) + div.at (je, ic + 1)));
        o.at (je, ic) = flux2.at (je, ic)
                        + dy * d2 * (Up.at (je, ilo + ic - 1) - Up.at (je - 1, ilo + ic - 1));
      }
  return o;
}
static A2 method19 (const A2 &U, const A2 &f1, const A2 &f2, int nc1, int nc2,
                    int ilo, double dtdx, double dtdy)
{
  A2 o (1, nc2, 1, nc1);
  for (int j = 1; j <= nc2; j++)
    for (int i = 1; i <= nc1; i++)
      o.at (j, i) = U.at (j, ilo + i - 1)
                    + dtdx * (f1.at (j, i) - f1.at (j, i + 1))
                    + dtdy * (f2.at (j, i) - f2.at (j + 1, i));
  return o;
}

// ---- one complete step: PhysBnd + Method ---------------------------------
struct Step { A2 u1, u2, u3, u4; };
static Step ref_step (const A2 &in1, const A2 &in2, const A2 &in3, const A2 &in4,
                      int nx, int ny, int niter, int godorder, double gamma,
                      double difmag, double dx, double dy, double dt,
                      bool xper, bool yper)
{
  const int nc1 = nx, nc2 = ny, ilo = 1;
  const double small = 1e-6, smallr = 1e-6, xi = 0.0;
  const double gm1 = gamma - 1.0;
  const double dtdx = dt / dx, dtdy = dt / dy;
  const double hdtdx = 0.5 * dtdx, hdtdy = 0.5 * dtdy;

  A2 W1 = physbnd (in1, nx, ny, xper, yper);
  A2 W2 = physbnd (in2, nx, ny, xper, yper);
  A2 W3 = physbnd (in3, nx, ny, xper, yper);
  A2 W4 = physbnd (in4, nx, ny, xper, yper);

  Prim q = method1 (W1, W2, W3, W4, nc1, nc2);
  A2 psml (1 - NCX, nc2 + NCX, 1 - NCX, nc1 + NCX);
  A2 p (1 - NCX, nc2 + NCX, 1 - NCX, nc1 + NCX);
  method2 (q, nc1, nc2, small, gm1, psml, p);
  A2 c = method3 (gamma, p, q.rho, nc1, nc2);
  A2 flatn = flaten (p, q.u, q.v, nc1, nc2, godorder);

  Slopes dp = slope (p, flatn, nc1, nc2);
  Slopes drho = slope (q.rho, flatn, nc1, nc2);
  Slopes du = slope (q.u, flatn, nc1, nc2);
  Slopes dv = slope (q.v, flatn, nc1, nc2);

  Face L = method5 (c, q.u, q.rho, q.v, p, psml, drho, dp, du, dv, nc1, nc2,
                    dtdx, hdtdx, smallr);
  Face R = method6 (c, q.u, q.rho, q.v, p, psml, drho, dp, du, dv, nc1, nc2,
                    dtdx, hdtdx, smallr);
  Face B = method7 (c, q.v, q.u, q.rho, p, psml, drho, dp, du, dv, nc1, nc2,
                    dtdy, hdtdy, smallr);
  Face T = method8 (c, q.v, q.u, q.rho, p, psml, drho, dp, du, dv, nc1, nc2,
                    dtdy, hdtdy, smallr);

  Flux4 f2a = method9 (B, T, psml, nc1, nc2, niter, gamma, xi);
  Flux4 f1a = method10 (L, R, psml, nc1, nc2, niter, gamma, xi);

  Face L2 = method11_12 (L, f2a, nc1, nc2, hdtdy, smallr, gm1, small, false);
  Face R2 = method11_12 (R, f2a, nc1, nc2, hdtdy, smallr, gm1, small, true);
  Face B2 = method13_14 (B, f1a, nc1, nc2, hdtdx, smallr, gm1, small, false);
  Face T2 = method13_14 (T, f1a, nc1, nc2, hdtdx, smallr, gm1, small, true);

  Flux4 f1c = method15 (L2, R2, psml, nc1, nc2, niter, gamma, xi);
  Flux4 f2c = method16 (B2, T2, psml, nc1, nc2, niter, gamma, xi);
  Flux4 f2d = transpose4 (f2c, 1, nc2 + 1, 1, nc1);

  A2 div = method17 (q.u, q.v, nc1, nc2, difmag, dx, dy);

  const A2 *Us[4] = { &W1, &W2, &W3, &W4 };
  const A2 *F1[4] = { &f1c.f1, &f1c.f2, &f1c.f3, &f1c.f4 };
  const A2 *F2[4] = { &f2d.f1, &f2d.f2, &f2d.f3, &f2d.f4 };
  std::vector<A2> out;
  for (int k = 0; k < 4; k++)
    {
      A2 g1 = method18a (div, *F1[k], *Us[k], nc1, nc2, ilo, dx);
      A2 g2 = method18b (div, *F2[k], *Us[k], nc1, nc2, ilo, dy);
      out.push_back (method19 (*Us[k], g1, g2, nc1, nc2, ilo, dtdx, dtdy));
    }
  return Step { out[0], out[1], out[2], out[3] };
}

} // namespace uref
