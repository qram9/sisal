#ifndef ELEMENTWISE_REF_H
#define ELEMENTWISE_REF_H
// Reference helpers for elementwise / reduction groups.
//
// These groups used to compare against hand-picked constants -- sqrt of perfect
// squares, sin(0), abs of three values -- which verify the answer at points
// chosen because the answer was easy to write down.  Here the expectation is
// COMPUTED from the input by libm or the C operator, so the input set can be
// chosen to be awkward instead of convenient, and a wrong-but-stable result is
// caught.
//
// The comparison is the definition of the operation, applied independently:
// fabsf for abs, -x for negate, x << n for shift.  That is a real oracle for a
// compiler under test, since nothing here shares code with the generated
// program.

#include <cmath>
#include <cstdint>
#include <string>
#include <vector>

#include "sisal_runtime.h"

namespace ewref {

// Inputs deliberately awkward: negatives, zero, and fractions on both sides of
// an integer so floor and trunc cannot agree with each other.
inline const std::vector<float> &xs ()
{
  static const std::vector<float> v
      = { -3.75f, -2.5f, -1.0f, -0.25f, 0.0f, 0.25f, 1.0f, 2.5f, 7.75f };
  return v;
}
// Strictly positive, for sqrt and log.
inline const std::vector<float> &pos ()
{
  static const std::vector<float> v
      = { 0.0625f, 0.5f, 1.0f, 2.0f, 4.0f, 9.0f, 16.5f, 100.0f };
  return v;
}
inline const std::vector<int32_t> &ints ()
{
  static const std::vector<int32_t> v = { -7, -1, 0, 1, 3, 8, 15, 64 };
  return v;
}

inline sisal_array_t mkf (const std::vector<float> &v)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 8, v.size ());
  a.lower_bound[0] = 1;
  for (size_t i = 0; i < v.size (); i++) ((float *)a.data)[i] = v[i];
  return a;
}
inline sisal_array_t mkd (const std::vector<double> &v)
{
  sisal_array_t a = sisal_array_alloc_sized (1, 4, v.size (), sizeof (double));
  a.lower_bound[0] = 1;
  for (size_t i = 0; i < v.size (); i++) ((double *)a.data)[i] = v[i];
  return a;
}
inline sisal_array_t mki (const std::vector<int32_t> &v)
{
  sisal_array_t a = sisal_array_alloc_empty (1, 6, v.size ());
  a.lower_bound[0] = 1;
  for (size_t i = 0; i < v.size (); i++) ((int32_t *)a.data)[i] = v[i];
  return a;
}
inline sisal_array_t mkb (const std::vector<bool> &v)
{
  sisal_array_t a = sisal_array_alloc_sized (1, 1, v.size (), 1);
  a.lower_bound[0] = 1;
  for (size_t i = 0; i < v.size (); i++) ((unsigned char *)a.data)[i] = v[i];
  return a;
}

// r[i] == f(in[i]) for every i, and the size matches
template <class F>
bool unary_f (sisal_array_t r, const std::vector<float> &in, F f,
              float tol = 1e-5f)
{
  if ((size_t)r.size != in.size ()) return false;
  for (size_t i = 0; i < in.size (); i++)
    if (fabsf (((const float *)r.data)[i] - f (in[i])) > tol) return false;
  return true;
}
template <class F>
bool unary_d (sisal_array_t r, const std::vector<double> &in, F f,
              double tol = 1e-12)
{
  if ((size_t)r.size != in.size ()) return false;
  for (size_t i = 0; i < in.size (); i++)
    if (fabs (((const double *)r.data)[i] - f (in[i])) > tol) return false;
  return true;
}
template <class F>
bool unary_f2i (sisal_array_t r, const std::vector<float> &in, F f)
{
  if ((size_t)r.size != in.size ()) return false;
  for (size_t i = 0; i < in.size (); i++)
    if (((const int32_t *)r.data)[i] != f (in[i])) return false;
  return true;
}
template <class F>
bool binary_f (sisal_array_t r, const std::vector<float> &a,
               const std::vector<float> &b, F f, float tol = 1e-5f)
{
  if ((size_t)r.size != a.size ()) return false;
  for (size_t i = 0; i < a.size (); i++)
    if (fabsf (((const float *)r.data)[i] - f (a[i], b[i])) > tol) return false;
  return true;
}
template <class F>
bool binary_i (sisal_array_t r, const std::vector<int32_t> &a, F f)
{
  if ((size_t)r.size != a.size ()) return false;
  for (size_t i = 0; i < a.size (); i++)
    if (((const int32_t *)r.data)[i] != f (a[i])) return false;
  return true;
}
// bool results are 1 byte
template <class F>
bool pred_f (sisal_array_t r, const std::vector<float> &a,
             const std::vector<float> &b, F f)
{
  if ((size_t)r.size != a.size ()) return false;
  for (size_t i = 0; i < a.size (); i++)
    if ((bool)((const unsigned char *)r.data)[i] != f (a[i], b[i]))
      return false;
  return true;
}
template <class F>
bool pred_b (sisal_array_t r, const std::vector<bool> &a,
             const std::vector<bool> &b, F f)
{
  if ((size_t)r.size != a.size ()) return false;
  for (size_t i = 0; i < a.size (); i++)
    if ((bool)((const unsigned char *)r.data)[i] != f (a[i], b[i]))
      return false;
  return true;
}

}  // namespace ewref
#endif
