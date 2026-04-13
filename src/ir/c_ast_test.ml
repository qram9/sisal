open C_ast
open C_ast_print

let test_binary_expression () =
  let e1 = BinOp (Sub, Id "a", Id "b") in
  let e2 = BinOp (Sub, Id "a", Id "b") in
  let e3 = BinOp (Add, e1, e2) in
  Printf.printf "Binary Expression Test: %s\n" (string_of_expr e3)

let test_if_statement () =
  let cond = BinOp (Gt, Id "a", LitInt 0) in
  let then_body = [
    Decl (Basic "int", "y", None);
    Expr (BinOp (AssignAdd, Id "a", Id "b"))
  ] in
  let if_stmt = If (cond, then_body, []) in
  Printf.printf "If Statement Test:\n%s\n" (string_of_stmt 0 if_stmt)

let test_for_loop () =
  let init = Decl (Basic "int", "i", Some (LitInt 0)) in
  let cond = BinOp (Le, Id "i", LitInt 100) in
  let step = UnaryOp (PostInc, Id "i") in
  let body = [
    Decl (Basic "int", "y", None);
    Expr (BinOp (Assign, Id "y", Id "i"))
  ] in
  let for_loop = For (init, cond, step, body) in
  Printf.printf "For Loop Test:\n%s\n" (string_of_stmt 0 for_loop)

let test_procedure () =
  let proc = {
    return_ty = Basic "int";
    name = "my_proc";
    params = [(Basic "int", "x"); (Basic "float", "y")];
    body = [
      Return (Some (BinOp (Add, Id "x", Cast (Basic "int", Id "y"))))
    ];
    extern_c = false;
  } in
  Printf.printf "Procedure Test:\n%s\n" (string_of_procedure proc)

let test_modern_features () =
  let vec_ty = Vector (Basic "float", 32) in
  let pragma = Pragma "omp parallel for simd" in
  let v_decl = Decl (vec_ty, "v", Some (Call ("v_load", [Id "ptr"]))) in
  let unit = {
    filename = "test.c";
    includes = ["stdio.h"; "omp.h"];
    globals = [v_decl; pragma];
    procedures = []
  } in
  Printf.printf "Modern Features Test:\n%s\n" (string_of_unit unit)

let run_tests () =
  test_binary_expression ();
  print_newline ();
  test_if_statement ();
  print_newline ();
  test_for_loop ();
  print_newline ();
  test_procedure ();
  print_newline ();
  test_modern_features ()

let () = run_tests ()
