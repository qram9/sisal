# GPU Tiling Optimization and CUTLASS Integration Proposal

This document outlines a proposal and architectural plan for integrating **GPU Tiling Optimizations** into the Sisal compiler's C++ code-generation pipeline using NVIDIA’s **CUTLASS** and **CuTe** libraries. It describes how to bridge Sisal’s dynamic, multidimensional APL-like arrays (`array_dv`) with GPU register tiles, define tiling parameters at the language level, and execute optimized matrix operations on modern GPU hardware (such as the RTX 3070).

---

## 1. Bridging `sisal_array_t` to CuTe Tensors

In the Sisal runtime, multidimensional arrays are represented using `sisal_array_t`. This structure defines data layouts dynamically:

```cpp
typedef struct {
    void* data;
    uint64_t size;
    int32_t rank;
    int32_t type_id;
    int32_t ref_count;
    uint32_t elem_bytes;
    int64_t lower_bound[8];
    int64_t dims[8];
    int64_t stride[8]; // Byte strides
} sisal_array_t;
```

To bridge a dynamic `sisal_array_t` to a `cute::Tensor` in the generated C++ code:

1.  **Virtual Origin Pointer Shift (0-based Indexing):** Sisal supports arbitrary lower bounds (e.g., 1-based indexing). Since CuTe is strictly 0-indexed, we shift the base data pointer to the virtual origin:
    $$\text{shifted\_ptr} = \text{data} - \sum (\text{lower\_bound}[i] \times \text{stride}[i])$$
2.  **Stride Conversion:** Sisal uses byte strides, whereas CuTe uses element strides. We divide each stride by the element byte-size:
    $$\text{element\_stride}[i] = \frac{\text{stride}[i]}{\text{elem\_bytes}}$$

### C++ Helper Construct
```cpp
template <typename T>
auto make_cute_tensor_from_sisal(const sisal_array_t& a) {
    using namespace cute;

    // 1. Shift base pointer for custom lower bounds
    char* byte_ptr = static_cast<char*>(a.data);
    for (int i = 0; i < a.rank; ++i) {
        byte_ptr -= (a.lower_bound[i] * a.stride[i]);
    }
    T* shifted_data = reinterpret_cast<T*>(byte_ptr);

    // 2. Build shape and element strides dynamically
    // (Assuming rank-2 for demonstration; easily extensible via switches or templates)
    auto shape  = make_shape(a.dims[0], a.dims[1]);
    auto stride = make_stride(a.stride[0] / sizeof(T), a.stride[1] / sizeof(T));
    
    return make_tensor(shifted_data, make_layout(shape, stride));
}
```

---

## 2. Loop-Level Tiling: The `tiled(...)` Loop Generator

To give developers control over tiling parameters at the loop level without introducing complex pragma parsing or changing the frontend grammar, we propose using a **pseudo-function wrapper on the generator** (e.g., `for i in tiled(1, N, 128)`).

Because this syntax matches a standard function invocation, it compiles to a standard AST without parser changes.

### AST Structure
The syntax `for i in tiled(1, N, 128)` compiles to:
```ocaml
In_exp (
  Value_name ["i"], 
  Exp [
    Invocation (
      Function_name ["tiled"], 
      Arg (Exp [Constant (Int 1); Val (Value_name ["N"]); Constant (Int 128)])
    )
  ]
)
```

### Compiler Interception in `to_if1.ml`
Inside `do_in_exp`, the compiler pattern-matches this invocation, lowers the bounds as a standard `RANGEGEN` node, and attaches a metadata pragma carrying the tile size parameter:

```ocaml
| [ Ast.Invocation (Ast.Function_name [ "TILED" | "tiled" ], 
                    Ast.Arg (Ast.Exp [ lo_exp; hi_exp; tile_size_exp ])) ] ->
    
    // 1. Lower the loop range as a standard counted RANGEGEN
    let (rg, rp, rt), in_gr = bin_exp lo_exp hi_exp in_gr If1.RANGEGEN in
    
    // 2. Extract compile-time static tile size
    let tile_size =
      match tile_size_exp with
      | Ast.Constant (Ast.Int ts) -> ts
      | _ -> 0
    in
    
    // 3. Attach metadata pragma to the RANGEGEN node
    let in_gr =
      if tile_size > 0 then
        let updated_nmap =
          match If1.NM.find_opt rg in_gr.If1.nmap with
          | Some (If1.Simple (lab, sym, pin, pout, prags)) ->
              let tile_prag = If1.Name ("tile_" ^ string_of_int tile_size) in
              If1.NM.add rg (If1.Simple (lab, sym, pin, pout, tile_prag :: prags)) in_gr.If1.nmap
          | _ -> in_gr.If1.nmap
        in
        { in_gr with If1.nmap = updated_nmap }
      else in_gr
    in
    // ... complete RANGEGEN boundary outputs
```

---

## 3. Operator-Level Tiling: Functional Fused Contractions

For algebraic expressions, developers can specify layout-transformations and tiling directly on matrix operators:
```sisal
C := permute(tile(matmul(A, B), [128, 128, 8]), [1, 0, 2])
```

### Compile-Time Fusion
To avoid creating intermediate arrays in global memory (which violates functional array-slicing performance constraints), the compiler fuses this nested pattern during AST-to-IF1 lowering. It generates a single, high-level `INNERPRODUCT_NODE` containing the tiling and permutation configurations as metadata pragmas:

```
node 5: INNERPRODUCT_NODE inputs[A, B] output[C] pragma[Name "tile_128_128_8", Name "permute_1_0_2"]
```

### Einsum General Contractions
For general tensor contractions like `EINSUM("abkd,kdce->abce", A, B)`, the `EINSUM_NODE` is kept high-level all the way to C++ lowering:
1.  The compiler maps free indices (`a, b, c, e`) and contracted indices (`k, d`) into 2D spaces: $M=(a, b, d)$, $N=(c, e)$, and $K=(k)$.
2.  During C++ generation, it emits CuTe **layout reshaping/flattening** code (`make_layout(make_shape(make_shape(dim_a, dim_b, dim_d), dim_k))`) to feed the multi-dimensional tensors directly to CUTLASS.

---

## 4. Epilogue and Operator Fusion

Performing calculations (like activation functions or bias additions) on the intermediate result of a matrix multiplication before storing it to global memory is critical to GPU efficiency. We propose an explicit **`fuse`** operator to handle this:

```sisal
C := fuse(tile(matmul(A, B), [128, 128, 8]), relu, relu_params)
```

### AST Structure
This translates to a clean nested AST invocation with no parser changes required:
```ocaml
Invocation (
  Function_name ["fuse"],
  Arg (Exp [
    tile_matmul_ast;          (* Target computation *)
    Val (Value_name ["relu"]);(* Fusion Operator identifier *)
    relu_params_ast           (* Parameters (e.g. threshold or alpha coefficient) *)
  ])
)
```

### Compiler Interception in `to_if1.ml`
The compiler matches the `fuse` invocation during AST-to-IF1 lowering, lowers the parameters (like thresholds or bias tensors) as extra input ports, and attaches `fuse_` pragmas to the generated `INNERPRODUCT_NODE`:

```ocaml
| Ast.Invocation (Ast.Function_name ["fuse"], 
                  Ast.Arg (Ast.Exp [
                    Ast.Invocation (Ast.Function_name ["tile"], 
                                    Ast.Arg (Ast.Exp [
                                      (Ast.Matmul_exp (a, b) | Ast.Innerproduct_exp (a, b));
                                      Ast.Exp tile_shape_exprs
                                    ]));
                    Ast.Val (Ast.Value_name [op_name]);
                    params_expr
                  ])) ->

    let (an, ap, at), in_gr = do_simple_exp in_gr a in
    let (bn, bp, bt), in_gr = do_simple_exp in_gr b in
    let (pn, pp, pt), in_gr = do_simple_exp in_gr params_expr in

    let tile_prag = If1.Name ("tile_" ^ string_of_tile_shape tile_shape) in
    let fuse_prag = If1.Name ("fuse_" ^ op_name) in

    let (rn, rp, rt), in_gr =
      If1.add_node_2
        (`Simple (If1.INNERPRODUCT_NODE, [| ""; ""; "" |], [| "" |], [ tile_prag; fuse_prag ]))
        in_gr
    in
    // ... wire inputs: A (port 0), B (port 1), and params (port 2) ...
```

---

## 5. Code Generation & CUTLASS/SYCL/Vulkan APIs

By keeping `INNERPRODUCT_NODE` and `EINSUM_NODE` at a high level until the C++ lowering phase, the code generator can directly target backend library APIs.

### CUTLASS C++ Codegen with Epilogue Fusion
When compiling the `INNERPRODUCT_NODE` containing the `fuse_relu` pragma, the code generator maps it to a custom CUTLASS Epilogue Operator and passes the runtime parameters from input port 2 into the arguments structure:

```cpp
// 1. Define types and layouts derived from compile-time pragmas
using ThreadblockShape = cutlass::gemm::GemmShape<128, 128, 8>;
using WarpShape        = cutlass::gemm::GemmShape<64, 64, 8>;
using InstructionShape = cutlass::gemm::GemmShape<16, 8, 16>;

using LayoutA = cutlass::layout::RowMajor;
using LayoutB = cutlass::layout::ColumnMajor;
using LayoutC = cutlass::layout::RowMajor;

// Define Epilogue Operator using the parsed pragma
using EpilogueOutputOp = cutlass::epilogue::thread::LinearCombinationBiasValRelu<
    int32_t, InstructionShape::kN, int32_t, int32_t
>;

using Gemm = cutlass::gemm::device::Gemm<
    int32_t, LayoutA,
    int32_t, LayoutB,
    int32_t, LayoutC,
    ThreadblockShape,
    WarpShape,
    InstructionShape,
    EpilogueOutputOp
>;

// 2. Lowering wrapper
extern "C" sisal_array_t func_matmul_fused(sisal_array_t A, sisal_array_t B, sisal_array_t params) {
    int32_t M = A.dims[0]; int32_t N = B.dims[1]; int32_t K = A.dims[1];
    
    sisal_array_t C = sisal_array_alloc_empty(2, type_integer, M * N);
    C.dims[0] = M; C.dims[1] = N;

    // Retrieve fused parameter from input port 2 (e.g. ReLU alpha)
    float relu_alpha = *static_cast<float*>(params.data);

    Gemm gemm_op;
    typename Gemm::Arguments args(
        {M, N, K},
        {(int32_t*)A.data, A.stride[0]/4},
        {(int32_t*)B.data, B.stride[0]/4},
        {(int32_t*)C.data, C.stride[0]/4},
        {(int32_t*)C.data, C.stride[0]/4},
        {1.0f, 0.0f, relu_alpha} // Pass fusion parameters here!
    );

    gemm_op(args);
    return C;
}
```

---

## 6. Memory Reuse and CPU-GPU Synchronization Hazards

Because GPU kernel launches are asynchronous, the CPU thread returns immediately to execute subsequent Sisal instructions. 

If the Sisal compiler optimizes memory by reusing or freeing the backing pointer of $A$ or $B$ before the GPU has completed its work, it will result in data corruption. The runtime must implement CPU-GPU synchronization boundaries.

### Solution 1: CPU Stream Synchronization (Recommended)
Block the CPU thread immediately after the CUTLASS invocation, guaranteeing that the arrays are no longer needed by the GPU when control returns to the Sisal runtime:

```cpp
// Within the C++ generated wrapper:
cutlass::Status status = gemm_op(args);

// Block the CPU thread until the GPU finishes reading/writing the buffers
cudaStreamSynchronize(0); // or cudaDeviceSynchronize()
```

### Solution 2: Vulkan Fences
If targeting the Vulkan cooperative matrix backend, submit the commands and explicitly block the CPU using fences before allowing the pointers to be reused or freed:

```cpp
vkQueueSubmit(queue, 1, &submitInfo, fence);

// Wait for the GPU to signal completion
vkWaitForFences(device, 1, &fence, VK_TRUE, UINT64_MAX);
```

### Solution 3: Reference Count Pinning (Asynchronous Execution)
To enable asynchronous execution overlap, increment the `ref_count` of the source arrays (`A` and `B`) when submitting the GPU task to prevent the memory manager from freeing or reusing them. Register a stream callback on the GPU completion event to decrement the reference count once the GPU is done.

---

## 7. Hardware Testing Setup (RTX 3070 Compatibility)

The **NVIDIA GeForce RTX 3070** is an excellent target for testing these optimizations. 

### GPU Specifications
*   **Architecture:** Ampere
*   **Compute Capability:** `8.6 (sm_86)`
*   **Supported Features:** Second-generation Tensor Cores, asynchronous memory copies (`cp.async`), software-pipelined double buffering, and TF32/BF16 arithmetic.

### Environment & Toolchain Setup
To compile and test the generated code on an RTX 3070:
1.  **CUDA Toolkit:** Install CUDA Toolkit 11.1 or newer (CUDA 12+ recommended).
2.  **Compilation Commands:** Pass the specific GPU target flags to `nvcc`:
    ```bash
    nvcc -O3 -std=c++17 -arch=sm_86 -I/path/to/cutlass/include generated_code.cu -o matmul_test
    ```

### Broader Compatibility
The compiled C++ code can easily target other generations by adapting the compiler parameters:
*   **Hopper (`sm_90` / H100):** Leverages hardware TMA (Tensor Memory Accelerator) and Warp Specialization.
*   **Turing (`sm_75` / RTX 2080):** Targets first-generation Tensor Cores.
*   **SYCL Target (oneMKL):** The C++ backend can output `oneapi::mkl::blas::gemm` calls to target Intel GPUs (XMX) or CPU clusters (AMX).
*   **Vulkan Target (`coopmat`):** Maps the high-level operators to `coopmat` types and `coopMatMulAdd` instructions in GLSL/SPIR-V.
