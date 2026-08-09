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

Replace value type must match the array element type (no implicit numeric coercion; double_real into array of real):
  $ sisal unit/replace_wrong_type.sis 2>&1
  Replace element not the correct type: array is array_dv[REAL], value is DOUBLE near "" in file: unit/replace_wrong_type.sis (line 9: char 0..0)
  there was an error: Ir.If1.Sem_error("Replace element not the correct type: array is array_dv[REAL], value is DOUBLE")
  [1]

Replace value type must match the array element type (integer into array of real):
  $ sisal unit/replace_wrong_type_int.sis 2>&1
  Replace element not the correct type: array is array_dv[REAL], value is INTEGRAL near "" in file: unit/replace_wrong_type_int.sis (line 7: char 0..0)
  there was an error: Ir.If1.Sem_error("Replace element not the correct type: array is array_dv[REAL], value is INTEGRAL")
  [1]

Local function definition in a let binding (parallel-copy binding takes values only):
  $ sisal unit/let_local_fn.sis 2>&1
  Local function definitions are not supported in a let binding; define the function separately near "" in file: unit/let_local_fn.sis (line 13: char 0..0)
  there was an error: Ir.If1.Sem_error("Local function definitions are not supported in a let binding; define the function separately")
  [1]

Multi-bind arity is strict - 2 names cannot absorb 3 values (no implicit packing):
  $ sisal unit/let_arity_mismatch.sis 2>&1
  Definition binds 2 name(s) but its right-hand side produces 3 value(s); names and values must correspond one-to-one near "" in file: unit/let_arity_mismatch.sis (line 12: char 0..0)
  there was an error: Ir.If1.Sem_error("Definition binds 2 name(s) but its right-hand side produces 3 value(s); names and values must correspond one-to-one")
  [1]

A `when` mask on a CROSS gather is not an array_dv operation: masking compacts,
so the result is ragged rather than rectangular.  (It used to compile and drop
the mask silently, returning the full rectangular array.)
  $ sisal unit/masked_cross_gather.sis --c=/dev/null 2>&1 | grep '^error:'
  error: forall gather: a `when`/`unless` mask on a CROSS generator is not an array_dv operation -- masking compacts, so the surviving count is a property of the data and the result is ragged, not rectangular. Accumulate into a list and pack it once at the end (see test/e2e/backtrack_dv.sis).  An explicit extent (`array_dv(n) of ... when ...`) carries a mask on a SINGLE generator, but not across a cross.

Sizability: a DIRECTLY (inline) recursive type has no compile-time size, so it
cannot be an array_dv element.  (Recursion THROUGH an array_dv is sizable -- the
dope handle stops the size fold -- and is allowed: see member_dv in positive.t.)
  $ sisal unit/unsizable_dv_elem.sis 2>&1
  array_dv element is not sizable: type `ARR` places a directly (inline) recursive type in an array_dv, so its size fold does not terminate (box the recursive arm, or recurse through an array_dv/stream handle instead) near "" in file: unit/unsizable_dv_elem.sis (line 14: char 0..0)
  there was an error: Ir.If1.Sem_error("array_dv element is not sizable: type `ARR` places a directly (inline) recursive type in an array_dv, so its size fold does not terminate (box the recursive arm, or recurse through an array_dv/stream handle instead)")
  [1]

Unsizability propagates through MANY levels of wrapping (record/union/record/union
around the recursive type - every wrapper inherits the non-terminating fold):
  $ sisal unit/unsizable_dv_deep.sis 2>&1
  array_dv element is not sizable: type `ARR` places a directly (inline) recursive type in an array_dv, so its size fold does not terminate (box the recursive arm, or recurse through an array_dv/stream handle instead) near "" in file: unit/unsizable_dv_deep.sis (line 31: char 0..0)
  there was an error: Ir.If1.Sem_error("array_dv element is not sizable: type `ARR` places a directly (inline) recursive type in an array_dv, so its size fold does not terminate (box the recursive arm, or recurse through an array_dv/stream handle instead)")
  [1]

The offending array_dv can be buried anywhere in the definition, not just at top:
  $ sisal unit/unsizable_dv_buried.sis 2>&1
  array_dv element is not sizable: type `DEEP` places a directly (inline) recursive type in an array_dv, so its size fold does not terminate (box the recursive arm, or recurse through an array_dv/stream handle instead) near "" in file: unit/unsizable_dv_buried.sis (line 15: char 0..0)
  there was an error: Ir.If1.Sem_error("array_dv element is not sizable: type `DEEP` places a directly (inline) recursive type in an array_dv, so its size fold does not terminate (box the recursive arm, or recurse through an array_dv/stream handle instead)")
  [1]

`old` in a returns clause.  It parses (the grammar has return_clause_old) but
has no meaning: a RETURNS is evaluated once per value of the loop's history and
the first of those is the seed, which has no previous iteration.  OSC 13.0.3
does not lower it either -- its frontend reports 0 semantic errors and then
if1ld aborts.
  $ sisal unit/returns_old.sis 2>&1 | grep '^there was'
  there was an error: Ir.If1.Sem_error("`old` is not allowed in a returns clause: a RETURNS is evaluated once per value of the loop's history, and the first of those is the seed, which has no previous iteration to read.  Bind the previous value to a carry in the loop body and return that instead")

