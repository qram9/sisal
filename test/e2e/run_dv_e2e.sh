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
    if ${CXX_BASE} -DTEST_${macro} "${HARNESS}" "${REPO}/test/e2e/numpy_verify.cpp" "${src}" -o "${bin}" \
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
run_group MATMUL_OP_DV      dv_matmul            ""
run_group MATMUL_DV         matmul_dv            ""

run_group FOR_INITIAL_DV    for_initial_dv       ""
run_group FORALL_DV_AT      forall_dv_at         ""
run_group FORALL_DV_CROSS   forall_dv_cross      ""
run_group FORALL_DV_DOT     forall_dv_dot        ""
run_group FORALL_DV_DOT3    forall_dv_dot3       ""
run_group THREE             three                ""
run_group FACT              fact                 ""
run_group RECORD_E2E        record_e2e           ""
run_group TAGCASE_E2E       tagcase_e2e          ""
run_group COMPLEX_FEATURES_E2E complex_features_e2e ""
run_group COMPLEX_OPS_E2E    complex_ops_e2e       ""
run_group IF_ONE            if_one               ""
run_group IF_TWO            if_two               ""
run_group IF_ELSEIF         if_elseif            ""
run_group MR_TWO_SCALAR     mr_two_scalar        ""
run_group LET_MULTI_BIND    let_multi_bind       ""
run_group LET_SEQ_BIND      let_seq_bind         ""
run_group XFA_B2_COND       xfa_b2_cond          ""
run_group AGGREGATE_ADD     aggregate_add        ""
run_group AREA              area                 ""
run_group MULTIDECL         multidecl            ""
run_group LOOPCARRY_USED    loopcarry_used       ""
run_group LOOPCARRY_IDENTITY loopcarry_identity  ""
run_group SUB_2D            sub_2d               ""
run_group SUB_3D            sub_3d               ""
run_group SLICE_DOTDOT      slice_dotdot         ""
run_group SUB_2D_DIAG       sub_2d_diag          ""
run_group LET_NESTED_SEQ    let_nested_seq       ""
run_group FORTY2            forty2               ""
run_group XFA_B1_DECLDEF    xfa_b1_decldef       ""
run_group XFA_C3_3AXIS      xfa_c3_3axis         ""
run_group SLICE_STORE       slice_store          ""
run_group MR_TWO_ARRAY      mr_two_array         ""
run_group AA                aa                   ""
run_group SUB_MATMUL        sub_matmul           ""
run_group PI                pi                   ""
run_group TST_LOOP1_DV      tst_loop1_dv         ""
run_group LOOP2_INNER       loop2_inner_dv       ""
run_group LOOP1_DV          loop1_dv             ""
run_group LOOP3_DV          loop3_dv             ""
run_group LOOP7_DV          loop7_dv             ""
run_group LOOP12_DV         loop12_dv            ""
run_group LOOP24_DV         loop24_dv            ""
run_group LOOP9_DV          loop9_dv             ""
run_group LOOP10_DV         loop10_dv            ""
run_group LOOP21_DV         loop21_dv            ""
run_group LOOP2_DV          loop2_dv             ""
run_group LOOP2S_DV         loop2s_dv            ""
run_group LOOP6_DV          loop6p_dv            ""
run_group LOOP4_DV          loop4p_dv            ""
run_group MR2_INIT          mr2_init_dv          ""
run_group LOOP16_DV         loop16p_dv           ""
run_group LOOP13_DV         loop13_dv            ""
run_group LOOP5_DV          loop5_dv             ""
run_group LOOP11S_DV         loop11s_dv           ""
run_group LOOP17_DV          loop17_dv            ""
run_group LOOP15_DV          loop15_dv            ""
run_group LOOP22_DV          loop22_dv            ""
run_group BUILDFILL_DV       buildfill_dv         ""
run_group LOOP20_DV          loop20_dv            ""
run_group CAP_NESTED_DV     cap_nested_dv        ""
run_group CAP_ARRAY_DV      cap_array_dv         ""
run_group CAP_FORINIT_DV    cap_forinit_dv       ""
run_group MR_FORALL_DV      mr_forall_dv         ""
run_group MR_FORINIT_DV     mr_forinit_dv        ""
run_group MR_1D2D_DV        mr_1d2d_dv           ""
run_group FN_MULTIOUT_DV    fn_multiout_dv       ""
run_group IF_MULTIOUT_DV    if_multiout_dv       ""
run_group FNCALL_FORALL_DV  fncall_forall_dv     ""
run_group NESTED_FORALL_DV  nested_forall_dv     ""
run_group CAP_2DEEP_DV      cap_2deep_dv         ""
run_group FN3RANK_DV        fn3rank_dv           ""
run_group IFTUPLE_FORALL_DV iftuple_forall_dv    ""
run_group RED_RANKS_DV      red_ranks_dv         ""
run_group RED_OPS_DV        red_ops_dv           ""
run_group RED_ARR_DV        red_arr_dv           ""
run_group BCAST3D_DV        bcast3d_dv           ""
run_group BCAST31_DV        bcast31_dv           ""
run_group IP_DV             ip_dv                ""
run_group CONV_DV           conv_dv              ""
run_group LAPLACE_DV        laplace_dv           ""
run_group SHAPED_GATHER_DV  shaped_gather_dv     ""
run_group FORINIT_MAT_GATHER_DV forinit_mat_gather_dv ""
run_group SCATTER_AT_DV     scatter_at_dv        ""
run_group GROW_NEST_DV      grow_nest_dv         ""
run_group TRANSPOSE_AT_DV   transpose_at_dv      ""
run_group FORALL_ROWSCATTER_DV forall_rowscatter_dv ""
run_group SMOOTH_DV         smooth_dv            ""
run_group DFT_DV            dft_dv               ""
run_group RECORD_OPS_DV     record_ops_dv        ""
run_group LOOP19S_DV         loop19s_dv           ""
run_group LOOP14_DV          loop14_dv            ""
run_group LOOP23S_DV         loop23s_dv           ""
run_group LOOP18P_DV         loop18p_dv           ""
run_group LOOP8P_DV          loop8p_dv            ""
run_group RED_SUM           red_sum              ""
run_group RED_PRODUCT       red_product          ""
run_group RED_GREATEST      red_greatest         ""
run_group RED_LEAST         red_least            ""
run_group RED_ARGMAX        red_argmax           ""
run_group RED_ARGMIN        red_argmin           ""
run_group RED_SUM_CROSS     red_sum_cross        ""
run_group FOR_INITIAL       for_initial_e2e      ""
run_group GAUSSJ_PARTS       gaussj_parts         ""
run_group GAUSSJ             gaussj_dv_rr         ""
run_group SWAPLOOP           swaploop             ""
run_group BROADCAST_PARTS    broadcast_parts      ""
run_group IF_COND            if_cond              ""
run_group FORALL_DV_SIMPLE   forall_dv_simple     ""
run_group CROSS_DV_DEMO      cross_dv_demo        ""
run_group FORALL_NEGATE      forall_negate        ""
run_group RANK8_SLICES       dv_rank8_slices      ""
run_group NEWTON_RAPHSON    newton_raphson       ""
run_group FEO_FFT_PARTS1    feo_fft_parts1       ""
run_group FEO_FFT_PARTS2    feo_fft_parts2       ""
run_group FEO_FFT_PARTS3    feo_fft_parts3       ""
run_group FEO_FFT_PARTS4    feo_fft_parts4       ""
run_group FEO_FFT_DV        feo_fft_dv           ""
run_group FEO_FFT           feo_fft              ""

echo "========================================"
echo "Groups passed: ${TOTAL_PASS}  Groups with failures: ${TOTAL_FAIL}"
echo "========================================"
[ ${TOTAL_FAIL} -eq 0 ]
