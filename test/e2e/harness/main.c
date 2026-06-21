#include <stdio.h>
#include <stdlib.h>

#define MAX_RANK 5

typedef struct {
    double* data;
    int rank;
    int shape[MAX_RANK];
    int strides[MAX_RANK];
} DopeVector;

// Helper to create a DopeVector (Row-Major)
DopeVector create_dv(double* data, int rank, int* shape) {
    DopeVector dv;
    dv.data = data;
    dv.rank = rank;
    int current_stride = 1;
    // For row-major, strides move from right to left
    for (int i = rank - 1; i >= 0; i--) {
        dv.shape[i] = shape[i];
        dv.strides[i] = current_stride;
        current_stride *= shape[i];
    }
    return dv;
}

void add_dv_demo(DopeVector A, DopeVector B) {
    int max_rank = (A.rank > B.rank) ? A.rank : B.rank;
    int res_shape[MAX_RANK];
    int total_elements = 1;

    printf("--- Setup Phase ---\n");
    printf("Array A Rank: %d, Shape: [", A.rank);
    for(int i=0; i<A.rank; i++) printf("%d%s", A.shape[i], i==A.rank-1?"":", ");
    printf("]\n");

    printf("Array B Rank: %d, Shape: [", B.rank);
    for(int i=0; i<B.rank; i++) printf("%d%s", B.shape[i], i==B.rank-1?"":", ");
    printf("]\n\n");

    // 1. Calculate Result Shape and Total Elements (Iterate 1 to MaxRank)
    for (int lfi = 1; lfi <= max_rank; lfi++) {
        // Trailing-axis alignment logic (LFI - (MaxRank - Rank))
        int idx_a = lfi - (max_rank - A.rank);
        int idx_b = lfi - (max_rank - B.rank);

        int size_a = (idx_a >= 1) ? A.shape[idx_a - 1] : 1;
        int size_b = (idx_b >= 1) ? B.shape[idx_b - 1] : 1;

        // Broadcasting rule: sizes must match or one must be 1
        int res_dim = (size_a > size_b) ? size_a : size_b;
        res_shape[lfi - 1] = res_dim;
        total_elements *= res_dim;
    }

    // 2. Prepare "Broadcast Strides" for the traversal
    // If a dimension is missing or size is 1, its stride is effectively 0.
    int b_stride_a[MAX_RANK] = {0}, b_stride_b[MAX_RANK] = {0};
    for (int lfi = 1; lfi <= max_rank; lfi++) {
        int idx_a = lfi - (max_rank - A.rank);
        int idx_b = lfi - (max_rank - B.rank);

        if (idx_a >= 1 && A.shape[idx_a - 1] > 1) 
            b_stride_a[lfi - 1] = A.strides[idx_a - 1];
        
        if (idx_b >= 1 && B.shape[idx_b - 1] > 1) 
            b_stride_b[lfi - 1] = B.strides[idx_b - 1];
    }

    printf("Result Shape: [");
    for(int i=0; i<max_rank; i++) printf("%d%s", res_shape[i], i==max_rank-1?"":", ");
    printf("]\n");
    printf("Total Elements to Process: %d\n\n", total_elements);

    printf("--- Execution Phase (Flat Loop) ---\n");
    for (int i = 0; i < total_elements; i++) {
        int offset_a = 0, offset_b = 0;
        int temp_i = i;

        // Decompose linear index 'i' into virtual coordinates and apply broadcast strides
        // We do this from right (fastest) to left (slowest)
        for (int d = max_rank - 1; d >= 0; d--) {
            int coord = temp_i % res_shape[d];
            offset_a += coord * b_stride_a[d];
            offset_b += coord * b_stride_b[d];
            temp_i /= res_shape[d];
        }

        double val_a = A.data[offset_a];
        double val_b = B.data[offset_b];
        
        printf("Linear Index %d | Result Coord: [%d, %d] | A_Offset: %d, B_Offset: %d | %g + %g = %g\n", 
               i, i / res_shape[1], i % res_shape[1], offset_a, offset_b, val_a, val_b, val_a + val_b);
    }
}

int main() {
    // Example: A[2, 3] + B[3]
    // A: [[10, 20, 30], [40, 50, 60]]
    // B: [1, 2, 3]
    double data_a[] = {10, 20, 30, 40, 50, 60}; 
    double data_b[] = {1, 2, 3};                
    
    int shape_a[] = {2, 3};
    int shape_b[] = {3};
    
    DopeVector dv_a = create_dv(data_a, 2, shape_a);
    DopeVector dv_b = create_dv(data_b, 1, shape_b);
    
    add_dv_demo(dv_a, dv_b);
    return 0;
}
