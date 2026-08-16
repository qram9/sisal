#ifndef DV_HARNESS_H
#define DV_HARNESS_H
// dv_harness.h -- everything shared by every e2e test group.
//
// Step 1 of the harness split (docs/e2e_harness_split_plan.md): the includes,
// the pass/fail accounting, the array constructors/accessors, the shared
// sort_big40 fixture, and main().  Each part file supplies run_active_test().
//
// g_no_macro, not a counter test, reports "no TEST_XXX defined".  Inferring it
// from `g_pass == 0 && g_fail == 0` looks equivalent and is not: array_swap_e2e
// runs, prints its own SUCCESS line and never calls check(), so a counter test
// declares it un-run.  The guard stays a compile-time `#if !defined(...)`, but
// each part lists only ITS OWN macros, so it is generated rather than
// maintained.

#include <algorithm>
#include <cmath>
#include <sisal_runtime.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <functional>
#include <vector>

#include "dv_rank8_slices_harness.h"
#include "kin16_ref.h"
#include "legpoly_ref.h"
#include "hilbert_ref.h"
#include "fft_ref.h"
#include "elementwise_ref.h"
#include "linalg_ref.h"

// ============================================================
// Pass/fail accounting
// ============================================================

static int g_pass = 0;
static int g_fail = 0;

static void
check (const char *name, bool cond)
{
  if (cond)
    {
      printf ("  PASS  %s\n", name);
      g_pass++;
    }
  else
    {
      printf ("  FAIL  %s\n", name);
      g_fail++;
    }
}

// ============================================================
// Approximate equality
// ============================================================

static inline bool
near_f (float a, float b)
{
  return fabsf (a - b) < 1e-4f;
}
static inline bool
near_d (double a, double b)
{
  return fabs (a - b) < 1e-9;
}

// ============================================================
// Array constructors
//
// sisal_array_alloc_empty sets lower_bound = 1.
// The generated code iterates indices starting at lower_bound and
// accesses data[idx - lower_bound], so lb=1 is required for input
// arrays too.  We replicate that here.
// ============================================================

static sisal_array_t
make_float_arr (const float *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 8, (uint64_t)n);
  // lower_bound already set to 1 by alloc_empty
  memcpy (a.data, data, (size_t)n * sizeof (float));
  return a;
}

static sisal_array_t
make_double_arr (const double *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 4, (uint64_t)n);
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}

static sisal_array_t
make_int_arr (const int32_t *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 6, (uint64_t)n);
  memcpy (a.data, data, (size_t)n * sizeof (int32_t));
  return a;
}

static sisal_array_t
make_bool_arr (const bool *data, int n)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 1, (uint64_t)n);
  memcpy (a.data, data, (size_t)n * sizeof (bool));
  return a;
}

// 2D row-major arrays.  After alloc_empty (which sets dims[0]=size for
// rank==1), we overwrite dims[0]/dims[1] for rank==2.
static sisal_array_t
make_float_2d (const float *data, int rows, int cols)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 8, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  memcpy (a.data, data, (size_t)n * sizeof (float));
  return a;
}

static sisal_array_t
make_double_2d (const double *data, int rows, int cols)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 4, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}

static sisal_array_t
make_double_2d_lb (const double *data, int rows, int cols, int lb0, int lb1)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 4, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  a.lower_bound[0] = lb0;
  a.lower_bound[1] = lb1;
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}static sisal_array_t
make_double_3d_lb (const double *data, int d0, int d1, int d2, int lb0, int lb1, int lb2)
{
  int n = d0 * d1 * d2;
  sisal_array_t a = sisal_array_alloc_empty (3, 4, (uint64_t)n);
  a.dims[0] = d0;
  a.dims[1] = d1;
  a.dims[2] = d2;
  a.lower_bound[0] = lb0;
  a.lower_bound[1] = lb1;
  a.lower_bound[2] = lb2;
  memcpy (a.data, data, (size_t)n * sizeof (double));
  return a;
}

static sisal_array_t
make_nested_double_2d (const double *data, int rows, int cols)
{
  sisal_array_t A = sisal_array_alloc_empty (1, 94, (uint64_t)rows);
  A.dims[0] = rows;
  for (int i = 0; i < rows; i++)
    {
      sisal_array_t row = sisal_array_alloc_empty (1, 4, (uint64_t)cols);
      row.dims[0] = cols;
      memcpy (row.data, data + i * cols, (size_t)cols * sizeof (double));
      ((sisal_array_t*)A.data)[i] = row;
    }
  return A;
}

static void
free_nested_double_2d (sisal_array_t A)
{
  for (int i = 0; i < A.size; i++)
    {
      sisal_array_t row = ((sisal_array_t*)A.data)[i];
      if (row.data) free (row.data);
    }
  if (A.data) free (A.data);
}

static sisal_array_t
make_int_2d (const int32_t *data, int rows, int cols)
{
  int n = rows * cols;
  sisal_array_t a = sisal_array_alloc_empty (2, 6, (uint64_t)n);
  a.dims[0] = rows;
  a.dims[1] = cols;
  memcpy (a.data, data, (size_t)n * sizeof (int32_t));
  return a;
}

// ============================================================
// Accessors for result arrays
// ============================================================

static inline float
af (sisal_array_t a, int i)
{
  return ((float *)a.data)[i];
}
static inline double
ad (sisal_array_t a, int i)
{
  return ((double *)a.data)[i];
}
static inline int32_t
ai (sisal_array_t a, int i)
{
  return ((int32_t *)a.data)[i];
}
static inline bool
ab (sisal_array_t a, int i)
{
  return ((bool *)a.data)[i];
}


// A 40-element scramble with negatives, duplicates and a wide value range --
// the substantive stress case; std::sort is the reference so any input is fair.
static const int32_t sort_big40[] = {
   37, -12,  85,   4,  85,  -7,  63,  21,  -99,  50,
    0,  17,  63,  -1,  42,  99, -55,   8,   8,  -3,
   71,  30, -40,  12,  60,  60,   5, -88,  33,  19,
  -12,  77,  46,  -6,  91,  24,  24, -70,  15,  -2,
};

// Set by run_active_test() when the part contains no active group.
static bool g_no_macro = false;

// Defined by whichever part file is being compiled.
void run_active_test (void);

int
main (void)
{
  printf ("=== dv_run_all test harness ===\n");
  run_active_test ();
  if (g_no_macro)
    {
      printf ("ERROR: No TEST_XXX macro defined.  Compile with e.g. "
              "-DTEST_ABS_DEMO\n");
      return 1;
    }
  printf ("\n--- Summary: %d passed, %d failed ---\n", g_pass, g_fail);
  return (g_fail > 0) ? 1 : 0;
}

#endif // DV_HARNESS_H
