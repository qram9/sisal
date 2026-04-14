Basic compilation tests - all should succeed with no output.

  $ sisal fact.sis
  $ sisal basic.sis
  $ sisal hello.sis
  $ sisal sieve.sis
  $ sisal queens.sis
  $ sisal empty.sis

Array of function types:
  $ sisal funcarray.sis
  $ sisal funcarray2.sis

Let bindings:
  $ sisal let_multi_bind.sis
  $ sisal let_seq_bind.sis
  $ sisal let_nested_seq.sis

Let rec - self recursion:
  $ sisal letrec.sis

Let rec - mutual recursion via AND:
  $ sisal letrec_mutual.sis
  $ sisal letrec_and_norec.sis
  $ sisal letrec_scope.sis

Lambdas:
  $ sisal capture.sis
  $ sisal capture2.sis
  $ sisal lambda_typed.sis
  $ sisal lambda_untyped.sis

Tuples:
  $ sisal tuple_tests.sis
  $ sisal tuple_add.sis
  $ sisal tuple_mixed.sis

APL bulk operations - reductions (SUM/PRODUCT/LEAST/GREATEST, range, for-loop):
  $ sisal apl_reduce.sis

APL bulk operations - MAP/FOLDL/FOLDR/SCAN and aliases (EACH, APPLY):
  $ sisal apl_map.sis
  $ sisal bulk_ops.sis

APL bulk operations - structural (TAKE/DROP/ROTATE/REVERSE/RAVEL/CONCAT/COMPRESS):
  $ sisal apl_structural.sis

DV_COMPRESS — COMPRESS produces array_dv; inputs may be monolithic or dv:
  $ sisal dv_compress_test.sis

APL bulk operations - sort and search (SORT/GRADE_UP/GRADE_DOWN/ARGMAX/ARGMIN/NONZERO/WHERE):
  $ sisal apl_sort_search.sis

APL bulk operations - statistics (MEAN/VARIANCE/STDDEV/ANY/ALL/NORM/CUMSUM/CUMPROD):
  $ sisal apl_stats.sis

APL bulk operations - shape (TILE/SQUEEZE/EXPAND/PAD/OUTERPRODUCT/PERMUTE):
  $ sisal apl_shape.sis

EINSUM tensor contraction (dot, matmul, matvec, outer, trace, transpose,
batched matmul, triple contraction, implicit output):
  $ sisal einsum_test.sis

APL bulk operations - case insensitivity (all ops work in lower and upper case):
  $ sisal apl_case.sis

APL bulk operations - mixing with forall loops (chaining, inline fns, nested):
  $ sisal apl_forall_mix.sis

Math builtins - scalar:
  $ sisal builtin_scalar.sis

Math builtins - vector (abs/max/min/mod/floor/trunc on float4/double4/int4):
  $ sisal builtin_vec.sis

Math builtins - matrix (abs/max/min/sin/cos/sqrt on mat2/mat4):
  $ sisal builtin_mat.sis

Records and unions:
  $ sisal record.sis
  $ sisal union.sis

DV array variants - array_dv OF with correct array_dv return types:
  $ sisal loop1_dv.sis
  $ sisal tst_loop1_dv.sis

Sorting algorithms:
  $ sisal bubble.sis
  $ sisal batcher.sis
  $ sisal heapsort.sis
  $ sisal mesort.sis
  $ sisal modern_heapsort.sis
  $ sisal quicksort.sis
  $ sisal quicksort1.sis
  $ sisal qs.sis
  $ sisal insertion1.sis
  $ sisal insertion2.sis

Queens / backtracking:
  $ sisal 8queens.sis
  $ sisal test_8queens.sis
  $ sisal newqueens.sis
  $ sisal alphabeta.sis
  $ sisal BackTrack.sis

For-loop variants:
  $ sisal for_all_reduce.sis
  $ sisal for_initial.sis
  $ sisal loop1.sis
  $ sisal loop2.sis
  $ sisal loop2s.sis
  $ sisal loop3.sis
  $ sisal loop4p.sis
  $ sisal loop5.sis
  $ sisal loop6p.sis
  $ sisal loop7.sis
  $ sisal loop8p.sis
  $ sisal loop9.sis
  $ sisal loop10.sis
  $ sisal loop11s.sis
  $ sisal loop12.sis
  $ sisal loop13.sis
  $ sisal loop14.sis
  $ sisal loop15.sis
  $ sisal loop16p.sis
  $ sisal loop17.sis
  $ sisal loop18p.sis
  $ sisal loop19s.sis
  $ sisal loop20.sis
  $ sisal loop21.sis
  $ sisal loop22.sis
  $ sisal loop23s.sis
  $ sisal loop24.sis
  $ sisal tst_loop1.sis
  $ sisal tst_loop2.sis
  $ sisal tst_loopAt.sis
  $ sisal tst_loopAt1.sis
  $ sisal tst_loopAt2.sis
  $ sisal tst_loopX.sis
  $ sisal tst_loopX2.sis
  $ sisal tst_loop_conv.sis

Dope-vector array agreement and arithmetic (Error Monad):
  $ sisal dv_agreement.sis

Matrix / linear algebra:
  $ sisal matmult.sis
  $ sisal matmult_dv.sis
  $ sisal mm.sis
  $ sisal mm_dv.sis
  $ sisal mmult2.sis
  $ sisal mat.sis
  $ sisal mat_construct.sis
  $ sisal mat_ip.sis
  $ sisal mat_ops.sis
  $ sisal mat2_construct.sis
  $ sisal mat2_ops.sis
  $ sisal mat3_construct.sis
  $ sisal mat3_ops.sis
  $ sisal mat4_construct.sis
  $ sisal mat4_ops.sis
  $ sisal innerproduct.sis
  $ sisal vec_ip.sis
  $ sisal vectest.sis
  $ sisal transpose.sis
  $ sisal transpose_dv.sis
  $ sisal reshape_1d_2d_1d.sis
  $ sisal reshape_3d.sis
  $ sisal reshape_matmul.sis
  $ sisal reshape_scan.sis
  $ sisal reshape_transpose.sis

Records and unions (extended):
  $ sisal record1.sis
  $ sisal record2.sis
  $ sisal tagcase.sis
  $ sisal tagcase_ii.sis
  $ sisal union0.sis
  $ sisal union1.sis
  $ sisal test_record1.sis

Higher-order functions and closures:
  $ sisal higher_order_fun.sis
  $ sisal closure3.sis
  $ sisal gclosure.sis
  $ sisal gmember.sis

Streams:
  $ sisal stream.sis

Numeric / math:
  $ sisal sqrt.sis
  $ sisal pi.sis
  $ sisal quad.sis
  $ sisal quadrature.sis
  $ sisal simpson.sis
  $ sisal idiv.sis
  $ sisal minmax.sis
  $ sisal random.sis
  $ sisal ranf.sis
  $ sisal ranfsamp.sis

DV variants of scientific benchmarks:
  $ sisal gaussj_perm_dv.sis
  $ sisal cfft_dv.sis
  $ sisal feo_fft_dv.sis
  $ sisal gaussj_dv.sis
  $ sisal hilbert_dv.sis
  $ sisal inverse_dv.sis
  $ sisal kin16_dv.sis
  $ sisal LegPoly_dv.sis
  $ sisal laplace_dv.sis
  $ sisal lu_npiv_dv.sis
  $ sisal lu_piv_dv.sis
  $ sisal newgauss_dv.sis
  $ sisal newgaussj_dv.sis
  $ sisal ricard_dv.sis
  $ sisal sp_dv.sis

Scientific benchmarks:
  $ sisal ada.sis
  $ sisal AngMom.sis
  $ sisal anneal.sis
  $ sisal area.sis
  $ sisal arsieve.sis
  $ sisal badfft.sis
  $ sisal bintree.sis
  $ sisal bmk11a.sis
  $ sisal bmk11ad.sis
  $ sisal cdf.sis
  $ sisal cfft.sis
  $ sisal choose.sis
  $ sisal ck_yb.sis
  $ sisal common.sis
  $ sisal conv.sis
  $ sisal CpxConv.sis
  $ sisal CpxFuncs.sis
  $ sisal crossovers.sis
  $ sisal crypto.sis
  $ sisal cyk.sis
  $ sisal data.sis
  $ sisal dft.sis
  $ sisal driver.sis
  $ sisal Energy.sis
  $ sisal faces.sis
  $ sisal fails.sis
  $ sisal fem.sis
  $ sisal feo.fft.sis
  $ sisal fft.sis
  $ sisal format.sis
  $ sisal forty2.sis
  $ sisal Freq.sis
  $ sisal fromC.sis
  $ sisal Gauss.sis
  $ sisal gaussdata.sis
  $ sisal gaussj_1.sis
  $ sisal gaussj.sis
  $ sisal gaussjnew.sis
  $ sisal genp.sis
  $ sisal gtransforms.sis
  $ sisal gurd.sis
  $ sisal ham.sis
  $ sisal hilbert.sis
  $ sisal IFg_2ETC.sis
  $ sisal IFg_3.sis
  $ sisal IFg_4.sis
  $ sisal IFm_2ETC.sis
  $ sisal IFm_3.sis
  $ sisal IFm_4.sis
  $ sisal Inital.sis
  $ sisal InitFFT.sis
  $ sisal initialize.sis
  $ sisal insert.sis
  $ sisal inside.sis
  $ sisal inverse.sis
  $ sisal job.sis
  $ sisal kin16.sis
  $ sisal laplace.sis
  $ sisal LegPoly.sis
  $ sisal life.sis
  $ sisal life1.sis
  $ sisal life2.sis
  $ sisal Linear.sis
  $ sisal long.sis
  $ sisal LTStep.sis
  $ sisal lu.npiv.sis
  $ sisal lu.piv.sis
  $ sisal lu.sis
  $ sisal main.sis
  $ sisal main4.sis
  $ sisal mainpara5.sis
  $ sisal mashi.sis
  $ sisal MdFFTFreq.sis
  $ sisal MdFFTGrid.sis
  $ sisal memberi.sis
  $ sisal memberii.sis
  $ sisal moldyn.sis
  $ sisal monolith.sis
  $ sisal multidecl.sis
  $ sisal nanu.sis
  $ sisal nested.sis
  $ sisal newfem.sis
  $ sisal newgauss.sis
  $ sisal newgaussj.sis
  $ sisal newsieve.sis
  $ sisal nico.sis
  $ sisal nico2.sis
  $ sisal noise.sis
  $ sisal noisedump.sis
  $ sisal nucleic.sis
  $ sisal oldcross.sis
  $ sisal out.sis
  $ sisal outs.sis
  $ sisal outs2.sis
  $ sisal p16final.sis
  $ sisal para.sis
  $ sisal parpi_babb.sis
  $ sisal parpi1.sis
  $ sisal parpi2.sis
  $ sisal PassFreq.sis
  $ sisal PassGrid.sis
  $ sisal pbatcher.sis
  $ sisal pinsert.sis
  $ sisal pinsertdata.sis
  $ sisal psa.sis
  $ sisal ricard.sis
  $ sisal Sas.sis
  $ sisal sbatcher.sis
  $ sisal scan1.sis
  $ sisal scan2.sis
  $ sisal scat.sis
  $ sisal send.sis
  $ sisal seqbatcher.sis
  $ sisal SIFuncs.sis
  $ sisal simple_tests.sis
  $ sisal simple.sis
  $ sisal simple2a.sis
  $ sisal simplebatcher.sis
  $ sisal sisal_tests_by_section.sis
  $ sisal slab.sis
  $ sisal smooth.sis
  $ sisal sp.init.sis
  $ sisal sp.sis
  $ sisal Spec.sis
  $ sisal Specam.sis
  $ sisal ssphot.sis
  $ sisal stand_alone_gauss.sis
  $ sisal successor.sis
  $ sisal switch.sis
  $ sisal swiz.sis
  $ sisal test_bin.sis
  $ sisal test_bin2.sis
  $ sisal test.sis
  $ sisal three.sis
  $ sisal trace.sis
  $ sisal transforms.sis
  $ sisal triple_tuple.sis
  $ sisal try_tup.sis
  $ sisal tsp.sis
  $ sisal tst.sis
  $ sisal tst1.sis
  $ sisal tst2.sis
  $ sisal tst3.sis
  $ sisal TStep.sis
  $ sisal tuple_fn_test.sis
  $ sisal tuple_fn_val.sis
  $ sisal tuple_hash_tests.sis
  $ sisal tuple_kw_tests.sis
  $ sisal tuple_mixed2.sis
  $ sisal tuple_mixed3.sis
  $ sisal types.sis
  $ sisal unsplit.sis
  $ sisal uprime1.sis
  $ sisal uprime2.sis
  $ sisal uprimemain.sis
  $ sisal UVSpec.sis
  $ sisal VSphere.sis
  $ sisal wordcount.sis
  $ sisal zbuffer1.sis
  $ sisal zbuffer2.sis
  $ sisal array_ex.sis
  $ sisal bad.sis
  $ sisal reset_ast.sis
  $ sisal rest_ast.sis
  $ sisal cross_dv_demo.sis
  $ sisal if_one.sis
  $ sisal if_two.sis
  $ sisal quadtree.sis
  $ sisal quadtypes.sis
  $ sisal complex_types.sis
