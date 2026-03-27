Basic compilation tests - all should succeed with no output.

  $ sisal fact.sis
  $ sisal basic.sis
  $ sisal hello.sis
  $ sisal sieve.sis
  $ sisal queens.sis

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

Records and unions:
  $ sisal record.sis
  $ sisal union.sis
