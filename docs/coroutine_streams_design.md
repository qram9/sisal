# Design Proposal: Cooperative Coroutine Streams in Sisal-to-C++ (Finalized)

This document establishes the finalized compile-time coroutine architecture for Sisal streams using **C++20 Coroutines (`co_yield`)**, replacing the legacy dynamically allocated ring-buffer implementation.

---

## 1. Why C++20 Coroutines were Selected (Final Decision)

After comparing three candidates—the legacy dynamic ring-buffer, POSIX `ucontext` (`swapcontext`), and C++20 coroutines—C++20 coroutines were chosen as the final architecture due to their overwhelming performance and compiler-level optimization advantages.

| Metric | Legacy Ring Buffer | POSIX `ucontext` | C++20 Coroutines (Final Choice) |
| :--- | :--- | :--- | :--- |
| **Model** | Eager (Buffered) | Stackful Cooperative | **Stackless Cooperative** |
| **Context Switch Cost** | None (sequential run) | High (~100–500 ns) | **Very Low (~2–5 ns)** |
| **Memory Footprint** | $O(N)$ heap buffer | $O(1)$ (requires $64\text{ KB}$ stack) | **$O(1)$ (minimal compiler frame)** |
| **System Calls** | None | Yes (saving/restoring signal masks) | **None** |
| **Lazy Evaluation** | No | Yes | **Yes** |

### Critical Performance Advantages:
1. **No Stack-Switching or System Calls**: Unlike POSIX `swapcontext`, which incurs a slow kernel transition to save/restore thread signal masks, C++20 coroutines perform context transitions purely in user space via basic jumps and state-index updates.
2. **Compiler-Optimized State Machine**: The C++ compiler transforms the coroutine into a highly optimized stackless state machine. It uses Heap Allocation Elision Optimization (HALO) to allocate only the exact live variables needed across yields, often optimizing the heap frame away completely.
3. **Execution Speed**: Switches run in **2 to 5 nanoseconds** (similar to a standard indirect function call), making them 30x to 100x faster than POSIX `ucontext`.

---

## 2. ucontext-based vs C++20 Coroutines Code Comparison

### Input Sisal Code
```sisal
global main(Limit: integer returns stream of integer)
  for initial
    I := 1;
  while I <= Limit repeat
    I := old I + 1;
  returns stream of I
  end for
end function
```

### Proposed C++20 Coroutine Lowering
The compiler will lower the stream generator function into a C++20 coroutine returning a custom generator type:

```cpp
#include <coroutine>

// Custom generator promise structure included in sisal_runtime.h
template<typename T>
struct sisal_generator {
    struct promise_type {
        T current_value;
        std::exception_ptr exception;

        sisal_generator get_return_object() {
            return sisal_generator(std::coroutine_handle<promise_type>::from_promise(*this));
        }
        std::suspend_always initial_suspend() { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }
        void unhandled_exception() { exception = std::current_exception(); }
        std::suspend_always yield_value(T value) {
            current_value = value;
            return {};
        }
        void return_void() {}
    };

    std::coroutine_handle<promise_type> h;
    sisal_generator(std::coroutine_handle<promise_type> h) : h(h) {}
    ~sisal_generator() { if (h) h.destroy(); }
    
    // Move-only semantics to support functional sharing safety
    sisal_generator(const sisal_generator&) = delete;
    sisal_generator& operator=(const sisal_generator&) = delete;
    sisal_generator(sisal_generator&& other) noexcept : h(other.h) { other.h = nullptr; }
    
    bool move_next() {
        if (h) { h.resume(); return !h.done(); }
        return false;
    }
    T current() const { return h.promise().current_value; }
};

// Lowered function
sisal_generator<int32_t> func_main(int32_t Limit) {
    // Seed element
    co_yield 1;
    
    int32_t I = 1;
    while (I <= Limit) {
        I = I + 1;
        co_yield I; // Yields next value and suspends
    }
}
```

---

## 3. Compiler Implementation Plan

To adopt this final design in the OCaml compiler (`apple_lower.ml`):

1. **Header Updates**: Add the standard `sisal_generator<T>` template definition to `sisal_runtime.h`.
2. **Port Lowering**: Change the output type signature of functions and subgraphs returning streams to `sisal_generator<T>`.
3. **Loop Translation**:
   * Lower the `RETURNS` subgraph of loops generating streams to C++20 coroutine blocks.
   * Translate seed writes and loop-body updates to `co_yield` statements instead of calling the legacy `sisal_stream_gather_store`.
4. **Consumer Lowering**:
   * Replace stream consumer references (`sisal_stream_first` and `sisal_stream_rest`) with iterator loops calling `move_next()` and `current()`.
