Basic compilation tests - all should succeed with no output.

  $ sisal unit/fact.sis
  $ sisal unit/basic.sis
  $ sisal unit/hello.sis
  $ sisal unit/sieve.sis
  $ sisal unit/queens.sis
  $ sisal unit/empty.sis

Array of function types:
  $ sisal unit/funcarray.sis
  $ sisal unit/funcarray2.sis

Let bindings:
  $ sisal unit/let_multi_bind.sis
  $ sisal unit/let_seq_bind.sis
  $ sisal unit/let_nested_seq.sis

Let rec - self recursion:
  $ sisal unit/letrec.sis

Let rec - mutual recursion via AND:
  $ sisal unit/letrec_mutual.sis
  $ sisal unit/letrec_and_norec.sis
  $ sisal unit/letrec_scope.sis

Lambdas:
  $ sisal unit/capture.sis
  $ sisal unit/capture2.sis
  $ sisal unit/lambda_typed.sis
  $ sisal unit/lambda_untyped.sis

Tuples:
  $ sisal unit/tuple_tests.sis
  $ sisal unit/tuple_add.sis
  $ sisal unit/tuple_mixed.sis

APL bulk operations - reductions (SUM/PRODUCT/LEAST/GREATEST, range, for-loop):
  $ sisal unit/apl/apl_reduce.sis

APL bulk operations - MAP/FOLDL/FOLDR/SCAN and aliases (EACH, APPLY):
  $ sisal unit/apl/apl_map.sis
  $ sisal unit/bulk_ops.sis

APL bulk operations - structural (TAKE/DROP/ROTATE/REVERSE/RAVEL/CONCAT/COMPRESS):
  $ sisal unit/apl/apl_structural.sis

DV_COMPRESS — COMPRESS produces array_dv; inputs may be monolithic or dv:
  $ sisal e2e/dv_lifted_arith.sis
  $ sisal e2e/dv_broadcast_complex.sis
  $ sisal e2e/dv_broadcast_numpy.sis
  $ sisal unit/verify_numpy_broadcast.sis
  $ sisal e2e/dv_compress_test.sis

APL bulk operations - sort and search (SORT/GRADE_UP/GRADE_DOWN/ARGMAX/ARGMIN/NONZERO/WHERE):
  $ sisal unit/apl/apl_sort_search.sis

APL bulk operations - statistics (MEAN/VARIANCE/STDDEV/ANY/ALL/NORM/CUMSUM/CUMPROD):
  $ sisal unit/apl/apl_stats.sis

APL bulk operations - shape (TILE/SQUEEZE/EXPAND/PAD/OUTERPRODUCT/PERMUTE):
  $ sisal unit/apl/apl_shape.sis

EINSUM tensor contraction (dot, matmul, matvec, outer, trace, transpose,
batched matmul, triple contraction, implicit output):
  $ sisal unit/einsum_test.sis

APL bulk operations - case insensitivity (all ops work in lower and upper case):
  $ sisal unit/apl/apl_case.sis

APL bulk operations - mixing with forall loops (chaining, inline fns, nested):
  $ sisal unit/apl/apl_forall_mix.sis

Math builtins - scalar:
  $ sisal unit/builtin_scalar.sis

Math builtins - vector (abs/max/min/mod/floor/trunc on float4/double4/int4):
  $ sisal unit/builtin_vec.sis

Math builtins - matrix (abs/max/min/sin/cos/sqrt on mat2/mat4):
  $ sisal unit/builtin_mat.sis

Records and unions:
  $ sisal unit/record.sis
  $ sisal unit/union.sis

DV array variants - array_dv OF with correct array_dv return types:
  $ sisal unit/loop1_dv.sis
  $ sisal unit/tst_loop1_dv.sis

Sorting algorithms:
  $ sisal unit/bubble.sis
  $ sisal unit/batcher.sis
  $ sisal unit/heapsort.sis
  $ sisal unit/mesort.sis
  $ sisal unit/modern_heapsort.sis
  $ sisal unit/quicksort.sis
  $ sisal unit/quicksort1.sis
  $ sisal unit/qs.sis
  $ sisal unit/insertion1.sis
  $ sisal unit/insertion2.sis

Queens / backtracking:
  $ sisal unit/8queens.sis
  $ sisal unit/test_8queens.sis
  $ sisal unit/newqueens.sis
  $ sisal unit/alphabeta.sis
  $ sisal unit/BackTrack.sis

For-loop variants:
  $ sisal unit/for_all_reduce.sis
  $ sisal unit/for_initial.sis
  $ sisal unit/loop1.sis
  $ sisal unit/loop2.sis
  $ sisal unit/loop2s.sis
  $ sisal unit/loop3.sis
  $ sisal unit/loop4p.sis
  $ sisal unit/loop5.sis
  $ sisal unit/loop6p.sis
  $ sisal unit/loop7.sis
  $ sisal unit/loop8p.sis
  $ sisal unit/loop9.sis
  $ sisal unit/loop10.sis
  $ sisal unit/loop11s.sis
  $ sisal unit/loop12.sis
  $ sisal unit/loop13.sis
  $ sisal unit/loop14.sis
  $ sisal unit/loop15.sis
  $ sisal unit/loop16p.sis
  $ sisal unit/loop17.sis
  $ sisal unit/loop18p.sis
  $ sisal unit/loop19s.sis
  $ sisal unit/loop20.sis
  $ sisal unit/loop21.sis
  $ sisal unit/loop22.sis
  $ sisal unit/loop23s.sis
  $ sisal unit/loop24.sis
  $ sisal unit/tst_loop1.sis
  $ sisal unit/tst_loop2.sis
  $ sisal unit/tst_loopAt.sis
  $ sisal unit/tst_loopAt1.sis
  $ sisal unit/tst_loopAt2.sis
  $ sisal unit/tst_loopX.sis
  $ sisal unit/tst_loopX2.sis
  $ sisal unit/tst_loop_conv.sis

Dope-vector array agreement and arithmetic (Error Monad):
  $ sisal e2e/dv_agreement.sis

Matrix / linear algebra:
  $ sisal unit/matmult.sis
  $ sisal unit/matmult_dv.sis
  $ sisal unit/mm.sis
  $ sisal unit/mm_dv.sis
  $ sisal unit/mmult2.sis
  $ sisal unit/mat.sis
  $ sisal unit/mat_construct.sis
  $ sisal unit/mat_ip.sis
  $ sisal unit/mat_ops.sis
  $ sisal unit/mat2_construct.sis
  $ sisal unit/mat2_ops.sis
  $ sisal unit/mat3_construct.sis
  $ sisal unit/mat3_ops.sis
  $ sisal unit/mat4_construct.sis
  $ sisal unit/mat4_ops.sis
  $ sisal unit/innerproduct.sis
  $ sisal unit/vec_ip.sis
  $ sisal unit/vectest.sis
  $ sisal unit/transpose.sis
  $ sisal unit/transpose_dv.sis
  $ sisal unit/reshape_1d_2d_1d.sis
  $ sisal unit/reshape_3d.sis
  $ sisal unit/reshape_matmul.sis
  $ sisal unit/reshape_scan.sis
  $ sisal unit/reshape_transpose.sis

Records and unions (extended):
  $ sisal unit/record1.sis
  $ sisal unit/record2.sis
  $ sisal unit/tagcase.sis
  $ sisal unit/tagcase_ii.sis
  $ sisal unit/union0.sis
  $ sisal unit/union1.sis
  $ sisal unit/test_record1.sis

Higher-order functions and closures:
  $ sisal unit/higher_order_fun.sis
  $ sisal unit/closure3.sis
  $ sisal unit/gclosure.sis
  $ sisal unit/gmember.sis

Streams:
  $ sisal unit/stream.sis

Numeric / math:
  $ sisal unit/sqrt.sis
  $ sisal unit/pi.sis
  $ sisal unit/quad.sis
  $ sisal unit/quadrature.sis
  $ sisal unit/simpson.sis
  $ sisal unit/idiv.sis
  $ sisal unit/minmax.sis
  $ sisal unit/random.sis
  $ sisal unit/ranf.sis
  $ sisal unit/ranfsamp.sis

Intrinsics lifted over array_dv (element-wise unary, binary, reductions):
  $ sisal e2e/dv_intrinsics.sis

Aggregate array_dv operations (basic.sis / sisal_tests_by_section.sis style):
  $ sisal unit/basic_dv.sis

DV variants of scientific benchmarks:
  $ sisal unit/gaussj_perm_dv.sis
  $ sisal unit/cfft_dv.sis
  $ sisal unit/feo_fft_dv.sis
  $ sisal unit/gaussj_dv.sis
  $ sisal unit/hilbert_dv.sis
  $ sisal unit/inverse_dv.sis
  $ sisal unit/kin16_dv.sis
  $ sisal unit/LegPoly_dv.sis
  $ sisal unit/laplace_dv.sis
  $ sisal unit/lu_npiv_dv.sis
  $ sisal unit/lu_piv_dv.sis
  $ sisal unit/newgauss_dv.sis
  $ sisal unit/newgaussj_dv.sis
  $ sisal unit/ricard_dv.sis
  $ sisal unit/sp_dv.sis

Scientific benchmarks:
  $ sisal unit/ada.sis
  $ sisal unit/AngMom.sis
  $ sisal unit/anneal.sis
  $ sisal unit/area.sis
  $ sisal unit/arsieve.sis
  $ sisal unit/badfft.sis
  $ sisal unit/bintree.sis
  $ sisal unit/bmk11a.sis
  $ sisal unit/bmk11ad.sis
  $ sisal unit/cdf.sis
  $ sisal unit/cfft.sis
  $ sisal unit/choose.sis
  $ sisal unit/ck_yb.sis
  $ sisal unit/common.sis
  $ sisal unit/conv.sis
  $ sisal unit/CpxConv.sis
  $ sisal unit/CpxFuncs.sis
  $ sisal unit/crossovers.sis
  $ sisal unit/crypto.sis
  $ sisal unit/cyk.sis
  $ sisal unit/data.sis
  $ sisal unit/dft.sis
  $ sisal unit/driver.sis
  $ sisal unit/Energy.sis
  $ sisal unit/faces.sis
  $ sisal unit/fails.sis
  $ sisal unit/fem.sis
  $ sisal unit/feo.fft.sis
  $ sisal unit/fft.sis
  $ sisal unit/format.sis
  $ sisal unit/forty2.sis
  $ sisal unit/Freq.sis
  $ sisal unit/fromC.sis
  $ sisal unit/Gauss.sis
  $ sisal unit/gaussdata.sis
  $ sisal unit/gaussj_1.sis
  $ sisal unit/gaussj.sis
  $ sisal unit/gaussjnew.sis
  $ sisal unit/genp.sis
  $ sisal unit/gtransforms.sis
  $ sisal unit/gurd.sis
  $ sisal unit/ham.sis
  $ sisal unit/hilbert.sis
  $ sisal unit/IFg_2ETC.sis
  $ sisal unit/IFg_3.sis
  $ sisal unit/IFg_4.sis
  $ sisal unit/IFm_2ETC.sis
  $ sisal unit/IFm_3.sis
  $ sisal unit/IFm_4.sis
  $ sisal unit/Inital.sis
  $ sisal unit/InitFFT.sis
  $ sisal unit/initialize.sis
  $ sisal unit/insert.sis
  $ sisal unit/inside.sis
  $ sisal unit/inverse.sis
  $ sisal unit/job.sis
  $ sisal unit/kin16.sis
  $ sisal unit/laplace.sis
  $ sisal unit/LegPoly.sis
  $ sisal unit/life.sis
  $ sisal unit/life1.sis
  $ sisal unit/life2.sis
  $ sisal unit/Linear.sis
  $ sisal unit/long.sis
  $ sisal unit/LTStep.sis
  $ sisal unit/lu.npiv.sis
  $ sisal unit/lu.piv.sis
  $ sisal unit/lu.sis
  $ sisal unit/main.sis
  $ sisal unit/main4.sis
  $ sisal unit/mainpara5.sis
  $ sisal unit/mashi.sis
  $ sisal unit/MdFFTFreq.sis
  $ sisal unit/MdFFTGrid.sis
  $ sisal unit/memberi.sis
  $ sisal unit/memberii.sis
  $ sisal unit/moldyn.sis
  $ sisal unit/monolith.sis
  $ sisal unit/multidecl.sis
  $ sisal unit/nanu.sis
  $ sisal unit/nested.sis
  $ sisal unit/newfem.sis
  $ sisal unit/newgauss.sis
  $ sisal unit/newgaussj.sis
  $ sisal unit/newsieve.sis
  $ sisal unit/nico.sis
  $ sisal unit/nico2.sis
  $ sisal unit/noise.sis
  $ sisal unit/noisedump.sis
  $ sisal unit/nucleic.sis
  $ sisal unit/oldcross.sis
  $ sisal unit/out.sis
  $ sisal unit/outs.sis
  $ sisal unit/outs2.sis
  $ sisal unit/p16final.sis
  $ sisal unit/para.sis
  $ sisal unit/parpi_babb.sis
  $ sisal unit/parpi1.sis
  $ sisal unit/parpi2.sis
  $ sisal unit/PassFreq.sis
  $ sisal unit/PassGrid.sis
  $ sisal unit/pbatcher.sis
  $ sisal unit/pinsert.sis
  $ sisal unit/pinsertdata.sis
  $ sisal unit/psa.sis
  $ sisal unit/ricard.sis
  $ sisal unit/Sas.sis
  $ sisal unit/sbatcher.sis
  $ sisal unit/scan1.sis
  $ sisal unit/scan2.sis
  $ sisal unit/scat.sis
  $ sisal unit/send.sis
  $ sisal unit/seqbatcher.sis
  $ sisal unit/SIFuncs.sis
  $ sisal unit/simple_tests.sis
  $ sisal unit/simple.sis
  $ sisal unit/simple2a.sis
  $ sisal unit/simplebatcher.sis
  $ sisal unit/sisal_tests_by_section.sis
  $ sisal unit/slab.sis
  $ sisal unit/smooth.sis
  $ sisal unit/sp.init.sis
  $ sisal unit/sp.sis
  $ sisal unit/Spec.sis
  $ sisal unit/Specam.sis
  $ sisal unit/ssphot.sis
  $ sisal unit/stand_alone_gauss.sis
  $ sisal unit/successor.sis
  $ sisal unit/switch.sis
  $ sisal unit/swiz.sis
  $ sisal unit/test_bin.sis
  $ sisal unit/test_bin2.sis
  $ sisal unit/test.sis
  $ sisal unit/three.sis
  $ sisal unit/trace.sis
  $ sisal unit/transforms.sis
  $ sisal unit/triple_tuple.sis
  $ sisal unit/try_tup.sis
  $ sisal unit/tsp.sis
  $ sisal unit/tst.sis
  $ sisal unit/tst1.sis
  $ sisal unit/tst2.sis
  $ sisal unit/tst3.sis
  $ sisal unit/TStep.sis
  $ sisal unit/tuple_fn_test.sis
  $ sisal unit/tuple_fn_val.sis
  $ sisal unit/tuple_hash_tests.sis
  $ sisal unit/tuple_kw_tests.sis
  $ sisal unit/tuple_mixed2.sis
  $ sisal unit/tuple_mixed3.sis
  $ sisal unit/types.sis
  $ sisal unit/unsplit.sis
  $ sisal unit/uprime1.sis
  $ sisal unit/uprime2.sis
  $ sisal unit/uprimemain.sis
  $ sisal unit/UVSpec.sis
  $ sisal unit/VSphere.sis
  $ sisal unit/wordcount.sis
  $ sisal unit/zbuffer1.sis
  $ sisal unit/zbuffer2.sis
  $ sisal unit/array_ex.sis
  $ sisal unit/bad.sis
  $ sisal unit/reset_ast.sis
  $ sisal unit/rest_ast.sis
  $ sisal unit/cross_dv_demo.sis
  $ sisal unit/if_one.sis
  $ sisal unit/if_two.sis
  $ sisal unit/quadtree.sis
  $ sisal unit/quadtypes.sis
  $ sisal unit/complex_types.sis
