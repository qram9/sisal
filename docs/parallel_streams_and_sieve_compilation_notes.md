# Sisal Stream Compilation and Parallel Sieve Research Notes

This document contains architectural notes, code sketches, and compiler design strategies for lowering Sisal `stream` types, conditional filter loops (`when`/`unless`), and parallel sieve algorithms to high-performance GPU (CUDA) and CPU (OpenMP) code.

---

## 1. The Parallel Sieve of Eratosthenes (GPU Friendly)

In traditional sequential implementations (like the original `sieve.sis` and `uprime1.sis`), the sieve is written using a dynamic pipeline of process filters. This model uses a sequential control loop (`for initial ... repeat`) to construct the filter stages one by one, which is highly serialized and not suitable for GPU execution.

To optimize the sieve for GPU parallelism, we eliminate the loop-carried dependencies by splitting the computation into two flat, embarrassingly parallel stages.

### A. Flat Two-Stage Parallel Sieve (GPU Optimized)
This is the most GPU-friendly implementation because it launches exactly two flat kernels, avoids recursive kernel overhead, and uses cache-friendly contiguous arrays.

```sisal
define main

type StrmInt = stream[ integer ];
type ArrInt  = array[ integer ];

global sqrt( a : double_real returns double_real )

% 1. Parallel Trial Division to find primes up to sqrt(Limit)
function ParallelSmallPrimes( MaxT: integer returns ArrInt )
   for x in 3, MaxT step 2
      
      % Check if x is prime by dividing by all odd numbers up to sqrt(x) in parallel
      is_prime := for d in 3, integer(sqrt(double_real(x))) step 2
                  returns value of all mod(x, d) <> 0
                  end for
                  
   returns array of x when is_prime
   end for
end function % ParallelSmallPrimes


% 2. Main Parallel Filter Loop
function main( Limit: integer returns StrmInt )
   let
      MaxT := integer( sqrt( double_real( Limit ) ) );
      
      % Compute small primes up to sqrt(Limit) in parallel
      Primes := ParallelSmallPrimes( MaxT );
   in
      % Check all odd numbers up to Limit in parallel against the small primes
      for x in 3, Limit step 2
         
         is_prime := for p in Primes
                     returns value of all mod(x, p) <> 0
                     end for
                     
      returns stream of x when is_prime
      end for
   end let
end function % main
```

### B. Recursive Square-Root Parallel Sieve
A mathematically elegant divide-and-conquer version that recursively takes the square root of the limit at each stage. While mathematically clean, it is less GPU-friendly due to dynamic parallelism and array concatenation (`||`) copy overheads.

```sisal
function RecursiveSieve( N: integer returns ArrInt )
   if N <= 3 then
      array[1: 2, 3] % Base case
   else
      let
         MaxT := integer( sqrt( double_real( N ) ) );
         SmallPrimes := RecursiveSieve( MaxT );
         
         RemainingPrimes := for x in MaxT + 1, N
                            is_odd := (mod(x, 2) <> 0);
                            is_prime := for p in SmallPrimes
                                        returns value of all mod(x, p) <> 0
                                        end for
                            returns array of x when (is_odd & is_prime)
                            end for
      in
         SmallPrimes || RemainingPrimes
      end let
   end if
end function
```

---

## 2. Universal GPU Compaction Template for `when` and `unless` Loops

Any Sisal loop containing a `when` or `unless` filter clause requires **Stream Compaction** because the number of output elements is dynamic. The compiler lowers these clauses systematically using GPU warp intrinsics (`__ballot_sync` and `__popc`).

### The Compilation Template:
For any loop:
```sisal
for I in Domain
returns stream/array of I when Condition(I)
end for
```

The compiler generates the following C++/CUDA logic:

1.  **Evaluate:** Each thread evaluates `bool keep = Condition(I);`.
2.  **Ballot:** The warp collects a 32-bit active bitmask: `unsigned int active_mask = __ballot_sync(0xFFFFFFFF, keep);`.
3.  **Scan:** Each thread calculates its local write offset:
    ```cpp
    unsigned int lower_threads = (1 << lane_id) - 1;
    int write_offset = __popc(active_mask & lower_threads);
    int warp_total = __popc(active_mask);
    ```
4.  **Write:**
    *   *If returning a Stream:* Write to Shared Memory and commit to the `cutlass::Pipeline`:
        ```cpp
        if (keep) smem_buffer[write_stage * TileSize + write_offset] = I;
        ```
    *   *If returning an Array:* Atomically acquire a global offset and write to VRAM:
        ```cpp
        __shared__ int global_base;
        if (lane_id == 0) global_base = atomicAdd(d_write_count, warp_total);
        __syncwarp();
        if (keep) d_global_array[global_base + write_offset] = I;
        ```

---

## 3. Pipeline Concurrency (The Fused GPU Shader Model)

In high-performance programs (such as `fem.sis` performing sparse matrix assembly), streams are compiled into **cooperative warp pipelines** inside the **same GPU compute shader (kernel)**. This completely avoids writing intermediate stream data to VRAM.

### Fused CUDA Block-Streaming Layout (derived from `fem.sis`):
Warp 0 calculates the element records (e.g. 16 sparse matrix coefficients per element) and commits them to Shared Memory. Warp 1 waits for the stage, reads the 16 elements, and applies them to the global buffer using hardware atomics.

```cpp
struct Chip {
    int x; int y; float val;
};

__global__ void fused_assembly_kernel(int numel, float* d_gstiff, int neq) {
    const int NumStages = 2;
    __shared__ Chip smem_chips[NumStages][16];
    __shared__ cuda::barrier<cuda::thread_scope_block> barrier;

    int warp_id = threadIdx.x / 32;
    int lane_id = threadIdx.x % 32;

    if (warp_id == 0) {
        // PRODUCER (Warp 0)
        int write_stage = 0;
        for (int lnum = 0; lnum < numel; ++lnum) {
            if (lane_id == 0) barrier.init(1);
            __syncwarp();

            if (lane_id < 16) {
                // Generate local stiffness record
                float val = compute_truss_val(lnum, lane_id);
                smem_chips[write_stage][lane_id] = Chip{x_coord, y_coord, val};
            }
            
            // Commit to pipeline
            cuda::memcpy_async(&smem_chips[write_stage], &smem_chips[write_stage], 0, barrier);
            write_stage = (write_stage + 1) % NumStages;
        }
    } else {
        // CONSUMER (Warp 1)
        int read_stage = 0;
        for (int lnum = 0; lnum < numel; ++lnum) {
            barrier.wait(); // Wait for data

            if (lane_id < 16) {
                Chip chip = smem_chips[read_stage][lane_id];
                if (chip.x > 0 && chip.y > 0) {
                    // Update global matrix using fast L2-hardware atomics
                    atomicAdd(&d_gstiff[(chip.x-1)*neq + (chip.y-1)], chip.val);
                }
            }
            __syncwarp();
            read_stage = (read_stage + 1) % NumStages;
        }
    }
}
```
