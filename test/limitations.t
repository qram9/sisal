Known compiler limitations — these tests pass by matching current failure output.
When a limitation is fixed, the output changes and this test "breaks" as a signal
to move the file to positive.t.

INNERPRODUCT requires vec/mat typed arguments (plain array[T] not accepted):
  $ sisal bulk_ops.sis 2>&1
  there was an error: Ir.If1.Sem_error("innerproduct() requires mat or vec arguments")
    near line 131, col 18
  [1]

CROSS forall with array[..] OF produces nested array_dv rather than flat array_dv:
  $ sisal matmult_dv.sis 2>&1
  there was an error: Ir.If1.Sem_error("Return Type Mismatch: return value #1: Expected array_dv[DOUBLE] (#90), but found array_dv[array_dv[DOUBLE]] (#98)")
    near line 17, col 23
  [1]
  $ sisal transpose_dv.sis 2>&1
  there was an error: Ir.If1.Sem_error("Return Type Mismatch: return value #1: Expected array_dv[DOUBLE] (#90), but found array_dv[array_dv[DOUBLE]] (#96)")
    near line 14, col 28
  [1]

Multi-dimensional A[i,j] indexing into reshaped Array_dv not yet implemented:
  $ sisal mm_dv.sis 2>&1
   RMC[1, 1] Fails for 8
  there was an error: Ir.If1.Sem_error("Situation:REAL")
    near line 23, col 11
  [1]
  $ sisal reshape_3d.sis 2>&1
   VOL[1, 1, P] Fails for 4
  there was an error: Ir.If1.Sem_error("Situation:DOUBLE")
    near line 22, col 32
  [1]
  $ sisal reshape_matmul.sis 2>&1
   A[II, J] Fails for 8
  there was an error: Ir.If1.Sem_error("Situation:REAL")
    near line 36, col 40
  [1]
  $ sisal reshape_scan.sis 2>&1
   MAT[D, D] Fails for 4
  there was an error: Ir.If1.Sem_error("Situation:DOUBLE")
    near line 22, col 32
  [1]
  $ sisal reshape_transpose.sis 2>&1
   A2D[C, R] Fails for 4
  there was an error: Ir.If1.Sem_error("Situation:DOUBLE")
    near line 26, col 32
  [1]
