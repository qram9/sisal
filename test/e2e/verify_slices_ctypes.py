import sys
import os
import subprocess
import ctypes
import numpy as np

# Define the sisal_array_t struct in ctypes matching runtime/sisal_runtime.h
class SisalArray(ctypes.Structure):
    _fields_ = [
        ("data", ctypes.c_void_p),
        ("size", ctypes.c_uint64),
        ("rank", ctypes.c_int32),
        ("type_id", ctypes.c_int32),
        ("ref_count", ctypes.c_int32),
        ("lower_bound", ctypes.c_int64 * 8),
        ("dims", ctypes.c_int64 * 8),
        ("stride", ctypes.c_int64 * 8)
    ]

# Define the multi-output return struct from func_MAIN
class FuncRank8Results(ctypes.Structure):
    _fields_ = [
        ("res_0", SisalArray),
        ("res_1", SisalArray),
        ("res_2", ctypes.c_double),
        ("res_3", SisalArray),
        ("res_4", SisalArray),
        ("res_5", SisalArray)
    ]

def sisal_to_numpy(sa):
    # Mapping type_id to NumPy dtype
    # 4 -> double (float64)
    # 3 -> real (float32)
    # 6 -> integer (int32)
    dtype_map = {
        4: np.float64,
        3: np.float32,
        6: np.int32
    }
    dtype = dtype_map.get(sa.type_id, np.float64)
    
    if sa.size == 0:
        return np.empty(0, dtype=dtype)
        
    # Get shape and strides
    shape = [sa.dims[i] for i in range(sa.rank)]
    itemsize = np.dtype(dtype).itemsize
    strides = []
    current_stride = itemsize
    for dim in reversed(shape):
        strides.insert(0, current_stride)
        current_stride *= dim
    
    # Cast sa.data to a ctypes array pointer
    num_items = sa.size
    if dtype == np.float64:
        data_ptr = ctypes.cast(sa.data, ctypes.POINTER(ctypes.c_double * num_items))
    elif dtype == np.float32:
        data_ptr = ctypes.cast(sa.data, ctypes.POINTER(ctypes.c_float * num_items))
    else:
        data_ptr = ctypes.cast(sa.data, ctypes.POINTER(ctypes.c_int32 * num_items))
        
    # Create NumPy array sharing the memory buffer
    arr = np.ndarray(shape, dtype=dtype, buffer=data_ptr.contents, strides=strides)
    return arr.copy() # Make a safe copy of the data

def test_ctypes_slicing():
    print("=== Starting NumPy ctypes Verification ===")
    
    # 1. Compile Sisal file to C++
    print("1. Compiling Sisal code to C++...")
    try:
        subprocess.run(["dune", "exec", "--", "sisal", "--c=temp_gen.cpp", "test/e2e/dv_rank8_slices.sis"], check=True)
    except subprocess.CalledProcessError:
        print("Sisal compilation failed!", file=sys.stderr)
        return False
        
    # 2. Compile C++ to shared library (.so / .dylib)
    print("2. Compiling C++ to shared library...")
    so_name = "./temp_gen.so"
    cmd = ["clang++", "-shared", "-fPIC", "-std=c++17", "-I", "runtime", "-framework", "Accelerate", "-o", so_name, "temp_gen.cpp"]
    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError:
        print("Shared library compilation failed!", file=sys.stderr)
        return False
        
    # 3. Load the library using ctypes
    print("3. Loading shared library...")
    try:
        lib = ctypes.CDLL(so_name)
    except Exception as e:
        print(f"Failed to load shared library: {e}", file=sys.stderr)
        return False
        
    # 4. Set return type and call func_MAIN
    lib.func_MAIN.restype = FuncRank8Results
    print("4. Executing func_MAIN via ctypes...")
    r = lib.func_MAIN()
    
    # 5. Build original array in python to slice and compare
    A = np.zeros((2, 2, 2, 2, 2, 2, 2, 2))
    for d1 in range(2):
        for d2 in range(2):
            for d3 in range(2):
                for d4 in range(2):
                    for d5 in range(2):
                        for d6 in range(2):
                            for d7 in range(2):
                                for d8 in range(2):
                                    val = d1*128.0 + d2*64.0 + d3*32.0 + d4*16.0 + d5*8.0 + d6*4.0 + d7*2.0 + (d8 + 1.0)
                                    A[d1, d2, d3, d4, d5, d6, d7, d8] = val
                                    
    # Expected slices computed by NumPy
    exp_0 = A[0, :, 1, :, 0, :, 1, :]
    exp_1 = A[:, 1, 0, 1, 0, 1, 0, :]
    exp_2 = A[0, 0, 0, 0, 0, 0, 0, 0]
    exp_3 = A[:, :, :, :, :, :, :, :]
    exp_4 = A[0, 1, 0, 1, :, :, :, :]
    exp_5 = A[:, :, :, :, 0, 1, 0, 1]
    
    # 6. Verify outputs
    print("5. Verifying slice outputs...")
    
    actual_0 = sisal_to_numpy(r.res_0)
    actual_1 = sisal_to_numpy(r.res_1)
    actual_2 = r.res_2
    actual_3 = sisal_to_numpy(r.res_3)
    actual_4 = sisal_to_numpy(r.res_4)
    actual_5 = sisal_to_numpy(r.res_5)
    
    # Verification checks
    assert np.allclose(actual_0, exp_0), f"res_0 mismatch:\nSisal:\n{actual_0}\nNumPy:\n{exp_0}"
    assert np.allclose(actual_1, exp_1), f"res_1 mismatch:\nSisal:\n{actual_1}\nNumPy:\n{exp_1}"
    assert abs(actual_2 - exp_2) < 1e-5, f"res_2 mismatch: Sisal={actual_2}, NumPy={exp_2}"
    assert np.allclose(actual_3, exp_3), f"res_3 mismatch"
    assert np.allclose(actual_4, exp_4), f"res_4 mismatch"
    assert np.allclose(actual_5, exp_5), f"res_5 mismatch"
    
    print("NumPy ctypes Verification SUCCESSFUL!")
    
    # Cleanup
    for f in ["temp_gen.cpp", so_name]:
        if os.path.exists(f):
            os.remove(f)
            
    return True

if __name__ == "__main__":
    success = test_ctypes_slicing()
    sys.exit(0 if success else 1)
