Known compiler limitations — these tests pass by matching current failure output.
When a limitation is fixed, the output changes and this test "breaks" as a signal
to move the file to positive.t.

All previous limitations in this file have been addressed.

DV broadcast lowering — '__Array1' name collision when multiple broadcast
calls appear in the same function scope (including chained lifted arithmetic):

  $ sisal dv_lifted_arith.sis
  there was an error: Ir.If1.Sem_error("Collision: Name '__Array1' already defined in current or parent scope.")
    near line 8, col 6
  [1]
  $ sisal dv_broadcast_complex.sis
  there was an error: Ir.If1.Sem_error("Collision: Name '__Array1' already defined in current or parent scope.")
    near line 8, col 6
  [1]
  $ sisal dv_broadcast_numpy.sis
  there was an error: Ir.If1.Sem_error("Collision: Name '__Array1' already defined in current or parent scope.")
    near line 11, col 6
  [1]
  $ sisal verify_numpy_broadcast.sis
  there was an error: Ir.If1.Sem_error("Collision: Name '__Array1' already defined in current or parent scope.")
    near line 8, col 6
  [1]
