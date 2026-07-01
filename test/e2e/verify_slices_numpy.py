import sys
import os
import subprocess
import random
import numpy as np

def run_test():
    print("=== Starting NumPy Differential Slicing Test ===")
    
    # 1. Choose a random rank from 2 to 8
    rank = random.randint(2, 8)
    shape = [random.randint(2, 3) for _ in range(rank)]
    total_size = int(np.prod(shape))
    print(f"Random array shape: {shape} (rank: {rank}, size: {total_size})")
    
    # 2. Populate a NumPy array with random float values
    A = np.random.uniform(1.0, 100.0, size=shape)
    flat_values = A.flatten()
    
    # 3. Choose a random slice specification
    # We must have at least one slice '..' (so the rank is not reduced to 0),
    # and at least one indexed dimension (to test index offset/strides).
    while True:
        specs = [] # list of (is_indexed, val_1_based)
        for i in range(rank):
            is_indexed = random.choice([True, False])
            if is_indexed:
                val = random.randint(1, shape[i])
                specs.append((True, val))
            else:
                specs.append((False, i))
        
        # Ensure we have at least one slice and at least one index
        has_index = any(s[0] for s in specs)
        has_slice = any(not s[0] for s in specs)
        if has_index and has_slice:
            break
            
    print(f"Slice specification: {['A[' + str(s[1]) + ']' if s[0] else '..' for s in specs]}")
    
    # Compute the expected NumPy slice result
    slice_indices = tuple(s[1] - 1 if s[0] else slice(None) for s in specs)
    expected_slice = A[slice_indices]
    expected_shape = list(expected_slice.shape)
    expected_rank = len(expected_shape)
    expected_flat = expected_slice.flatten()
    
    print(f"Expected shape: {expected_shape} (rank: {expected_rank}, size: {expected_flat.size})")
    
    # 4. Generate the Sisal code
    sisal_lines = []
    sisal_lines.append("define main")
    sisal_lines.append("type OneD = array_dv[double];")
    sisal_lines.append("type TwoD = array_dv[double];")
    
    # Generate the main function
    sisal_lines.append("function main(returns TwoD)")
    sisal_lines.append("  let")
    
    # Generate the flat values literal V
    val_strs = [f"{v:.6f}d0" for v in flat_values]
    sisal_lines.append(f"    V := array OneD [1: {', '.join(val_strs)}];")
    
    # Generate nested loops to build the multi-rank array A
    # A := for d1 in 1, S1
    #        r1 := ...
    for i in range(rank):
        indent = "    " + "  " * i
        loop_var = f"d{i+1}"
        sisal_lines.append(f"{indent}r{i} := for {loop_var} in 1, {shape[i]}")
        
    # Inside the innermost loop, compute the flat index
    indent = "    " + "  " * rank
    strides = []
    current_stride = 1
    for s in reversed(shape[1:]):
        current_stride *= s
        strides.insert(0, current_stride)
    strides.append(1)
    
    idx_terms = []
    for i in range(rank):
        idx_terms.append(f"(d{i+1} - 1) * {strides[i]}")
    
    sisal_lines.append(f"{indent}idx := { ' + '.join(idx_terms) } + 1;")
    sisal_lines.append(f"{indent}val := V[idx];")
    
    # Return the nested loop gathers
    # returns array_dv of val
    # end for
    for i in reversed(range(rank)):
        indent = "    " + "  " * i
        res_var = "val" if i == rank - 1 else f"r{i+1}"
        sisal_lines.append(f"{indent}returns array_dv of {res_var}")
        sisal_lines.append(f"{indent}end for;")
        
    # Wire the slice
    # A := r0;
    # slice_res := A[spec];
    sisal_lines.append("    A := r0;")
    
    spec_strs = []
    for s in specs:
        if s[0]:
            spec_strs.append(str(s[1]))
        else:
            spec_strs.append("..")
            
    sisal_lines.append(f"    slice_res := A[{', '.join(spec_strs)}];")
    sisal_lines.append("  in")
    sisal_lines.append("    slice_res")
    sisal_lines.append("  end let")
    sisal_lines.append("end function")
    
    sisal_code = "\n".join(sisal_lines)
    
    # Write to a temporary file
    with open("temp_gen.sis", "w") as f:
        f.write(sisal_code)
        
    # 5. Compile to C++ using our Sisal compiler
    print("Compiling Sisal code to C++...")
    try:
        subprocess.run(["dune", "exec", "--", "sisal", "--c=temp_gen.cpp", "temp_gen.sis"], check=True)
    except subprocess.CalledProcessError as e:
        print("Sisal compilation failed!", file=sys.stderr)
        print("Generated Sisal code:\n", sisal_code)
        return False
        
    # 6. Generate the C++ test driver
    driver_code = """#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include "sisal_runtime.h"

extern "C" sisal_array_t func_MAIN();

int main() {
    sisal_array_t r = func_MAIN();
    printf("RESULT_RANK: %d\\n", r.rank);
    printf("RESULT_SIZE: %llu\\n", r.size);
    printf("RESULT_LB: %d\\n", (int)r.lower_bound[0]);
    printf("RESULT_DIM: %d\\n", (int)r.dims[0]);
    
    double* d = (double*)r.data;
    printf("RESULT_DATA: ");
    for (uint64_t i = 0; i < r.size; i++) {
        printf("%s%f", i > 0 ? ", " : "", d[i]);
    }
    printf("\\n");
    return 0;
}
"""
    with open("temp_driver.cpp", "w") as f:
        f.write(driver_code)
        
    # 7. Compile the C++ program
    print("Compiling C++ test binary...")
    cmd = ["clang++", "-std=c++17", "-I", "runtime", "-framework", "Accelerate", "-o", "temp_run", "temp_gen.cpp", "temp_driver.cpp"]
    res_comp = subprocess.run(cmd, capture_output=True, text=True)
    if res_comp.returncode != 0:
        print("C++ compilation failed!", file=sys.stderr)
        print("C++ Compiler Output:\n", res_comp.stderr, file=sys.stderr)
        return False
        
    # 8. Run the binary and parse the results
    print("Running test binary...")
    res = subprocess.run(["./temp_run"], capture_output=True, text=True)
    if res.returncode != 0:
        print("Execution failed!", file=sys.stderr)
        print(res.stderr, file=sys.stderr)
        return False
        
    lines = res.stdout.strip().split("\n")
    results = {}
    for line in lines:
        if ":" in line:
            k, v = line.split(":", 1)
            results[k.strip()] = v.strip()
            
    res_rank = int(results["RESULT_RANK"])
    res_size = int(results["RESULT_SIZE"])
    res_data = [float(x) for x in results["RESULT_DATA"].split(",")]
    
    # 9. Verify against NumPy expected values
    print("Verifying outputs against NumPy...")
    print(f"Sisal rank: {res_rank}, size: {res_size}")
    print(f"Sisal data: {res_data}")
    print(f"NumPy data: {list(expected_flat)}")
    
    assert res_rank == expected_rank, f"Rank mismatch: {res_rank} != {expected_rank}"
    assert res_size == expected_flat.size, f"Size mismatch: {res_size} != {expected_flat.size}"
    
    for i in range(len(res_data)):
        diff = abs(res_data[i] - expected_flat[i])
        assert diff < 1e-5, f"Value mismatch at index {i}: {res_data[i]} != {expected_flat[i]} (diff: {diff})"
        
    print("Verification SUCCESSFUL! Sisal slice output matches NumPy exactly!")
    
    # Cleanup temporary files
    for f in ["temp_gen.sis", "temp_gen.cpp", "temp_driver.cpp", "temp_run"]:
        if os.path.exists(f):
            os.remove(f)
            
    return True

if __name__ == "__main__":
    success = run_test()
    sys.exit(0 if success else 1)
