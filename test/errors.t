Error message tests - check that the compiler produces helpful diagnostics.

Forward reference in let block (left cannot see right):
  $ sisal unit/let_no_fwd_ref.sis 2>&1
  Undefined name 'X': not in scope. In a 'let' block, names can only reference bindings defined earlier - forward references are not allowed. near "" in file: unit/let_no_fwd_ref.sis (line 7: char 0..0)
  there was an error: Ir.If1.Sem_error("Undefined name 'X': not in scope. In a 'let' block, names can only reference bindings defined earlier - forward references are not allowed.")
  [1]

Parse error - using = instead of := in let:
  $ echo "FUNCTION F(RETURNS INTEGER) LET X = 1 IN X END LET END FUNCTION" | sisal 2>&1
  Parse error in <stdin>, line 1, col 34:
    Expected ':=' or ':' after name in let binding.
  [1]

Mixed Cross and Dot in forall generators (Cross then Dot):
  $ sisal unit/forall_dv_cross_dot.sis 2>&1
  Cross and Dot may not be mixed in a for loop. near "" in file: unit/forall_dv_cross_dot.sis (line 10: char 0..0)
  there was an error: Ir.If1.Sem_error("Cross and Dot may not be mixed in a for loop.")
  [1]

Mixed Cross and Dot in forall generators (Dot then Cross):
  $ sisal unit/forall_dv_dot_cross.sis 2>&1
  Cross and Dot may not be mixed in a for loop. near "" in file: unit/forall_dv_dot_cross.sis (line 10: char 0..0)
  there was an error: Ir.If1.Sem_error("Cross and Dot may not be mixed in a for loop.")
  [1]
