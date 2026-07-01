#ifndef NUMPY_VERIFY_H
#define NUMPY_VERIFY_H

#include <vector>
#include <string>
#include "sisal_runtime.h"

// verify_slice_numpy
// Validates a resulting sisal_array_t against the expected result calculated by NumPy.
//
// Arguments:
//   shape      - The shape of the original source array (e.g. {2, 2, 2, 2, 2, 2, 2, 2})
//   flat_data  - The flattened data elements of the original source array
//   slice_spec - The slice specification, e.g. "[0, :, 1, :, 0, :, 1, :]"
//   actual     - The actual sisal_array_t slice output to be verified
//
// Returns true if actual rank, size, and all elements match NumPy exactly (within 1e-5 tolerance).
bool verify_slice_numpy(const std::vector<int>& shape,
                        const std::vector<double>& flat_data,
                        const std::string& slice_spec,
                        sisal_array_t actual);

#endif // NUMPY_VERIFY_H
