#include <iostream>
#include <vector>
#include <chrono>
#include "sisal_runtime.h"

// Prototypes for generated Sisal functions (Case matches generated aggregate_add.cpp)
extern "C" sisal_array_t VECTORADD_CPU(sisal_array_t A, sisal_array_t B);
extern "C" sisal_array_t VECTORADD_GPU(sisal_array_t A, sisal_array_t B);

int main() {
    const uint64_t N = 1024 * 1024 * 16; // 1M elements
    std::cout << "Starting Mixed C++/Sisal Vector Add Test (N=" << N << ")" << std::endl;

    // 1. Allocate Unified Memory (4KB aligned) via Runtime
    sisal_array_t A = sisal_alloc_unified(N * sizeof(float));
    sisal_array_t B = sisal_alloc_unified(N * sizeof(float));
    
    A.size = N;
    B.size = N;
    A.lower_bound = 1;
    B.lower_bound = 1;

    float* dataA = (float*)A.data;
    float* dataB = (float*)B.data;

    for(uint64_t i=0; i<N; ++i) {
        dataA[i] = 1.0f;
        dataB[i] = 2.0f;
    }

    std::cout << "Memory allocated and initialized." << std::endl;

    // 2. Call Sisal CPU (GCD optimized)
    auto start_cpu = std::chrono::high_resolution_clock::now();
    sisal_array_t res_cpu = VECTORADD_CPU(A, B);
    auto end_cpu = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff_cpu = end_cpu - start_cpu;
    std::cout << "CPU Sisal (GCD) took: " << diff_cpu.count() << "s" << std::endl;

    // 3. Call Sisal GPU (Metal optimized)
    auto start_gpu = std::chrono::high_resolution_clock::now();
    sisal_array_t res_gpu = VECTORADD_GPU(A, B);
    auto end_gpu = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff_gpu = end_gpu - start_gpu;
    std::cout << "GPU Sisal (Metal) took: " << diff_gpu.count() << "s" << std::endl;

    // 4. Verify results
    float* res_cpu_ptr = (float*)res_cpu.data;
    float* res_gpu_ptr = (float*)res_gpu.data;
    bool ok = true;
    for(uint64_t i=0; i<10; ++i) {
        if (res_cpu_ptr[i] != 3.0f || res_gpu_ptr[i] != 3.0f) {
            ok = false;
            std::cout << "Mismatch at " << i << ": CPU=" << res_cpu_ptr[i] << " GPU=" << res_gpu_ptr[i] << std::endl;
        }
    }

    if(ok) std::cout << "SUCCESS: CPU and GPU results match expected values!" << std::endl;
    else std::cout << "FAILURE: Results mismatch." << std::endl;

    return 0;
}
