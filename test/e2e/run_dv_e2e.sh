#!/bin/bash
# run_dv_e2e.sh — End-to-end regression for the 9 known-working dv_*.sis files.
# Rebuilds the compiler, re-emits C++ from source, compiles, and executes.
# Run from the repo root:  bash test/run_dv_e2e.sh

set -e

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
SISAL="${REPO}/_build/install/default/bin/sisal"
RUNTIME="${REPO}/runtime"
HARNESS="${REPO}/test/e2e/dv_run_all.cpp"
GENDIR="$(mktemp -d /tmp/sisal_e2e.XXXXXX)"
trap 'rm -rf "$GENDIR"' EXIT

CXX_BASE="clang++ -std=c++17 -I${RUNTIME} -framework Accelerate -DACCELERATE_NEW_LAPACK"

echo "=== Building compiler ==="
(cd "${REPO}" && dune build)
echo ""

# Compile one .sis to C++ and store in GENDIR
emit_c() {
    local stem=$1    # e.g. dv_abs_demo
    local flags=$2   # e.g. --dv
    local out="${GENDIR}/${stem}.cpp"
    "${SISAL}" "${REPO}/test/e2e/${stem}.sis" ${flags} --c="${out}" 2>/tmp/sisal_emit_err_${stem}.txt
    echo "${out}"
}

# Build and run one test group
TOTAL_PASS=0
TOTAL_FAIL=0

run_group() {
    local macro=$1       # e.g. ABS_DEMO
    local stem=$2        # e.g. dv_abs_demo
    local sis_flags=$3   # e.g. --dv
    local bin="${GENDIR}/test_${macro}"

    printf '%-44s ' "Emitting ${stem}.sis..."
    local src
    if src=$(emit_c "${stem}" "${sis_flags}" 2>&1); then
        echo -n "OK  |  "
    else
        echo "EMIT FAILED"
        cat /tmp/sisal_emit_err_${stem}.txt
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        return
    fi

    printf 'Building TEST_%-20s ' "${macro}..."
    if ${CXX_BASE} -DTEST_${macro} "${HARNESS}" "${src}" -o "${bin}" \
            2>/tmp/sisal_build_err_${macro}.txt; then
        echo -n "OK"
    else
        echo "BUILD FAILED"
        cat /tmp/sisal_build_err_${macro}.txt
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        return
    fi

    echo ""
    set +e
    "${bin}"
    local ret=$?
    set -e
    if [ $ret -eq 0 ]; then
        TOTAL_PASS=$((TOTAL_PASS + 1))
    else
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
    fi
    echo ""
}

run_group AGREEMENT         dv_agreement
run_group LIFTED_ARITH      dv_lifted_arith
run_group INTRINSICS        dv_intrinsics
run_group BROADCAST_COMPLEX dv_broadcast_complex
run_group COMPRESS          dv_compress_test
run_group BROADCAST_NUMPY   dv_broadcast_numpy
run_group FORALL_CPU        forall_cpu
run_group NEGATE_DV         negate_dv
run_group FORALL_REDUCE_DV  dv_forall_reduce
run_group BULK_BASIC        dv_bulk_basic
run_group INNERPRODUCT_DV   dv_innerproduct
run_group FOR_INITIAL       for_initial_e2e      ""
run_group GAUSSJ_PARTS       gaussj_parts         ""
run_group GAUSSJ             gaussj_dv_rr         ""
run_group SWAPLOOP           swaploop             ""
run_group GEN_EXTENT         gen_extent           ""
run_group BROADCAST_PARTS    broadcast_parts      ""
run_group IF_COND            if_cond              ""
run_group FORALL_DV_SIMPLE   forall_dv_simple     ""
run_group CROSS_DV_DEMO      cross_dv_demo        ""
run_group FORALL_NEGATE      forall_negate        ""

echo "========================================"
echo "Groups passed: ${TOTAL_PASS}  Groups with failures: ${TOTAL_FAIL}"
echo "========================================"
[ ${TOTAL_FAIL} -eq 0 ]
