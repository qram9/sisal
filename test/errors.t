Error message tests - check that the compiler produces helpful diagnostics.

Forward reference in let block (left cannot see right):
  $ sisal let_no_fwd_ref.sis 2>&1
  Undefined name 'X': not in scope. In a 'let' block, names can only reference bindings defined earlier - forward references are not allowed. near "" in file: let_no_fwd_ref.sis (line 7: char 0..0)
  there was an error: Ir.If1.Sem_error("Undefined name 'X': not in scope. In a 'let' block, names can only reference bindings defined earlier - forward references are not allowed.")
  [1]

Parse error - using = instead of := in let:
  $ echo "FUNCTION F(RETURNS INTEGER) LET X = 1 IN X END LET END FUNCTION" | sisal 2>&1
  Parse error in <stdin>, line 1, col 34:
    Expected ':=' or ':' after name in let binding.
  [1]
