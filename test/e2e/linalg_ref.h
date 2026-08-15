#ifndef LINALG_REF_H
#define LINALG_REF_H
// References for the dot / matmul groups.
//
// These compared against hand-computed products -- [[19,22],[43,50]] for one
// fixed 2x2 pair, 32 for one fixed dot, and for the 4-D case two spot values
// (1.23 and 4.93) out of a 144-element result.  Two samples of 144 is close to
// no check at all: a contraction that got the axis order wrong would still hit
// them by luck more often than not.
//
// INNERPRODUCT is numpy's np.dot (see the project notes: the DOT keyword is a
// forall generator and unrelated).  For N-D operands np.dot contracts the LAST
// axis of A with the SECOND-TO-LAST of B, giving
//     shape = A.shape[:-1] + B.shape[:-2] + B.shape[-1:]
// which is what ref_tensordot below computes, in the obvious O(n^k) way.

#include <cstdint>
#include <vector>

namespace laref {

template <class T>
T ref_dot (const std::vector<T> &a, const std::vector<T> &b)
{
  T s = 0;
  for (size_t i = 0; i < a.size (); i++) s += a[i] * b[i];
  return s;
}

// C[i,j] = sum_k A[i,k] * B[k,j], all row-major
template <class T>
std::vector<T> ref_matmul (const std::vector<T> &A, const std::vector<T> &B,
                           int M, int K, int N)
{
  std::vector<T> C ((size_t)M * N, T (0));
  for (int i = 0; i < M; i++)
    for (int j = 0; j < N; j++)
      {
        T s = 0;
        for (int k = 0; k < K; k++) s += A[(size_t)i * K + k] * B[(size_t)k * N + j];
        C[(size_t)i * N + j] = s;
      }
  return C;
}

// np.dot for arbitrary rank, row-major.  Contracts A's last axis with B's
// second-to-last.  Returns the flat result; `out_dims` receives its shape.
template <class T>
std::vector<T> ref_tensordot (const std::vector<T> &A,
                              const std::vector<int> &da,
                              const std::vector<T> &B,
                              const std::vector<int> &db,
                              std::vector<int> &out_dims)
{
  const int K = da.back ();
  // B of rank 1 is the special case: np.dot contracts its ONLY axis, so the
  // result is A.shape[:-1] with nothing appended.  Appending db.back() here
  // gave the wrong shape for 1D.1D, 2D.1D and 3D.1D.
  const bool b_vec = (db.size () == 1);
  out_dims.clear ();
  for (size_t i = 0; i + 1 < da.size (); i++) out_dims.push_back (da[i]);
  if (!b_vec)
    {
      for (size_t i = 0; i + 2 < db.size (); i++) out_dims.push_back (db[i]);
      out_dims.push_back (db.back ());
    }

  // outer extents
  size_t lead = 1;
  for (size_t i = 0; i + 1 < da.size (); i++) lead *= da[i];
  size_t midb = 1;
  if (!b_vec)
    for (size_t i = 0; i + 2 < db.size (); i++) midb *= db[i];
  const size_t N = b_vec ? 1 : db.back ();

  // A is [lead, K]; B is [midb, K, N]
  std::vector<T> C (lead * midb * N, T (0));
  for (size_t l = 0; l < lead; l++)
    for (size_t m = 0; m < midb; m++)
      for (size_t n = 0; n < N; n++)
        {
          T s = 0;
          for (int k = 0; k < K; k++)
            s += A[l * (size_t)K + k] * B[(m * (size_t)K + k) * N + n];
          C[(l * midb + m) * N + n] = s;
        }
  return C;
}

}  // namespace laref
#endif
