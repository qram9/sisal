#include "numpy_verify.h"
#include <iostream>
#include <sstream>
#include <cstdio>
#include <memory>
#include <cmath>
#include <cstdlib>

bool verify_slice_numpy(const std::vector<int>& shape,
                        const std::vector<double>& flat_data,
                        const std::string& slice_spec,
                        sisal_array_t actual) {
    // 1. Construct the Python code to run
    std::stringstream py_cmd;
    py_cmd << "python3 -c \"import numpy as np; import json; ";
    
    // Original flat data list
    py_cmd << "flat_data = [";
    for (size_t i = 0; i < flat_data.size(); ++i) {
        py_cmd << flat_data[i] << (i + 1 < flat_data.size() ? "," : "");
    }
    py_cmd << "]; ";
    
    // Shape list
    py_cmd << "shape = [";
    for (size_t i = 0; i < shape.size(); ++i) {
        py_cmd << shape[i] << (i + 1 < shape.size() ? "," : "");
    }
    py_cmd << "]; ";
    
    // Reconstruct and slice
    py_cmd << "A = np.array(flat_data).reshape(shape); ";
    py_cmd << "sliced = A" << slice_spec << "; ";
    
    // Output JSON representation of sliced array
    py_cmd << "out = {'rank': int(sliced.ndim), 'size': int(sliced.size), 'data': [float(x) for x in sliced.flatten()]}; ";
    py_cmd << "print(json.dumps(out))\"";
    
    // 2. Execute via popen
    std::string cmd = py_cmd.str();
    std::array<char, 256> buffer;
    std::string result;
    
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd.c_str(), "r"), pclose);
    if (!pipe) {
        std::cerr << "verify_slice_numpy: popen failed!" << std::endl;
        return false;
    }
    
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    
    if (result.empty()) {
        std::cerr << "verify_slice_numpy: No output from Python script!" << std::endl;
        return false;
    }
    
    // 3. Parse simple JSON output manually to avoid heavy JSON parser library dependencies
    // Expected output format: {"rank": R, "size": S, "data": [val0, val1, ...]}
    int py_rank = 0;
    long long py_size = 0;
    std::vector<double> py_data;
    
    size_t rank_pos = result.find("\"rank\":");
    if (rank_pos != std::string::npos) {
        py_rank = std::stoi(result.substr(rank_pos + 7));
    }
    
    size_t size_pos = result.find("\"size\":");
    if (size_pos != std::string::npos) {
        py_size = std::stoll(result.substr(size_pos + 7));
    }
    
    size_t data_pos = result.find("\"data\":");
    if (data_pos != std::string::npos) {
        size_t list_start = result.find("[", data_pos);
        size_t list_end = result.find("]", list_start);
        if (list_start != std::string::npos && list_end != std::string::npos) {
            std::string list_str = result.substr(list_start + 1, list_end - list_start - 1);
            std::stringstream ss(list_str);
            std::string val_str;
            while (std::getline(ss, val_str, ',')) {
                if (!val_str.empty()) {
                    py_data.push_back(std::stod(val_str));
                }
            }
        }
    }
    
    // 4. Compare with actual sisal_array_t
    if ((int)actual.rank != py_rank) {
        std::cerr << "verify_slice_numpy: Rank mismatch: actual=" << actual.rank << ", expected=" << py_rank << std::endl;
        return false;
    }
    if ((long long)actual.size != py_size) {
        std::cerr << "verify_slice_numpy: Size mismatch: actual=" << actual.size << ", expected=" << py_size << std::endl;
        return false;
    }
    
    double* actual_data = (double*)actual.data;
    for (long long i = 0; i < py_size; ++i) {
        double diff = std::abs(actual_data[i] - py_data[i]);
        if (diff > 1e-5) {
            std::cerr << "verify_slice_numpy: Mismatch at index " << i << ": actual=" << actual_data[i] << ", expected=" << py_data[i] << " (diff=" << diff << ")" << std::endl;
            return false;
        }
    }
    
    return true;
}
