#include <stdio.h>
#include <assert.h>
#include <memory>
#include <stdlib.h>
#include <string.h>

struct sisal_array_t {
    std::shared_ptr<float> data;
    size_t size;
};

// Custom deleter for posix_memalign
struct FreeDeleter {
    void operator()(float* p) const {
        printf("  [DEBUG] Freeing array data at %p\n", (void*)p);
        free(p);
    }
};

sisal_array_t sisal_array_alloc(size_t size) {
    void* ptr = NULL;
    posix_memalign(&ptr, 4096, size * sizeof(float));
    memset(ptr, 0, size * sizeof(float));
    printf("  [DEBUG] Allocated %zu floats at %p\n", size, ptr);
    
    sisal_array_t arr;
    arr.size = size;
    arr.data = std::shared_ptr<float>((float*)ptr, FreeDeleter());
    return arr;
}

// Pass by pointer so we can "steal" the reference if we are consuming it,
// OR we can pass by const reference if c_ast doesn't know about liveness.
// If c_ast doesn't do liveness, we CANNOT do in-place updates unless we
// explicitly clear the old variable before calling replace, OR we just 
// accept that everything is CoW.
// Wait! If we pass by value, the caller STILL HOLDS A REFERENCE.
// So without the caller saying "I am done with A", use_count will always be > 1.

// Let's implement an explicit "consume and replace" that the compiler could generate
// for loops: "B = sisal_array_consume_replace(&A, index, val);"

sisal_array_t sisal_array_consume_replace(sisal_array_t* arr_ptr, size_t index, float val) {
    // Steal the reference
    sisal_array_t result;
    result.data = std::move(arr_ptr->data); // Transfer ownership, ref count doesn't change!
    result.size = arr_ptr->size;
    
    // Now arr_ptr->data is empty (use_count = 0).
    // If the caller was the only owner, result.data.use_count() is now exactly 1.
    
    if (result.data.use_count() > 1) {
        printf("  [DEBUG] CoW Triggered! use_count=%ld. Copying array data.\n", result.data.use_count());
        void* new_ptr = NULL;
        posix_memalign(&new_ptr, 4096, result.size * sizeof(float));
        memcpy(new_ptr, result.data.get(), result.size * sizeof(float));
        result.data = std::shared_ptr<float>((float*)new_ptr, FreeDeleter());
    } else {
        printf("  [DEBUG] Exclusive ownership (use_count=1). Updating IN-PLACE!\n");
    }
    
    result.data.get()[index] = val;
    return result;
}

int main() {
    printf("--- Test 3: Consume and Replace (In-Place) ---\n");
    {
        sisal_array_t A = sisal_array_alloc(5);
        printf("A allocated. use_count=%ld\n", A.data.use_count());
        
        // This time, we pass the address of A to signify we are consuming it.
        // It will steal A's reference. Because no one else owns it, it updates IN PLACE.
        sisal_array_t B = sisal_array_consume_replace(&A, 0, 42.0f);
        
        printf("A use_count=%ld (A is now empty)\n", A.data.use_count());
        printf("B use_count=%ld\n", B.data.use_count());
        
        // What if we do a loop?
        for (int i = 1; i < 3; i++) {
            B = sisal_array_consume_replace(&B, i, 42.0f + i);
        }
    }
    printf("End of Test 3 block.\n\n");
    
    return 0;
}