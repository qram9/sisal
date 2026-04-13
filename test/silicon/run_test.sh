#!/bin/bash

# Sisal-to-Silicon Automation Script for M4 Max
# Usage: ./run_test.sh <sisal_file>

SISAL_FILE=$1
if [ -z "$SISAL_FILE" ]; then
    echo "Usage: ./run_test.sh <sisal_file>"
    exit 1
fi

echo "--- Step 1: Compiling Sisal to C++ ---"
dune exec sisal -- $SISAL_FILE --c > out_gen.cpp

if [ $? -ne 0 ]; then
    echo "ERROR: Sisal compilation failed."
    exit 1
fi

echo "--- Step 2: Compiling C++ to Silicon Binary ---"
clang++ -O3 out_gen.cpp test_runner.cpp -I. -framework Accelerate -o silicon_test

if [ $? -ne 0 ]; then
    echo "ERROR: C++ compilation failed."
    exit 1
fi

echo "--- Step 3: Executing on M4 Max ---"
./silicon_test

# Cleanup
rm out_gen.cpp silicon_test
