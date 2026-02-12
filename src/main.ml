module Lex = Fe.Lex
open Lexing
module Parse = Fe.Parse
module Ast = Ir.Ast
module If1 = Ir.If1
module To_if1_ = To_if1

let error msg lexbuf =
  let start = Lexing.lexeme_start_p lexbuf in
  let finish = Lexing.lexeme_end_p lexbuf in
  print_endline
    (Printf.sprintf
       ("%s in file: %s (line %d" ^^ ": char %d" ^^ "..%d)")
       msg start.pos_fname start.pos_lnum
       (start.pos_cnum - start.pos_bol)
       (finish.pos_cnum - finish.pos_bol))

let main () =
  let lexbuf =
    if Array.length Sys.argv > 1 then Lexing.from_channel (open_in Sys.argv.(1))
    else Lex.get_lex_buf
  in
  try
    let set_filename (fname : string) (lexbuf : Lexing.lexbuf) =
      lexbuf.Lexing.lex_curr_p <-
        { lexbuf.lex_curr_p with Lexing.pos_fname = fname };
      lexbuf
    in
    let sisal_ast =
      Parse.main Lex.sisal_lex (set_filename Sys.argv.(1) lexbuf)
    in
    print_endline (Ast.str_compilation_unit sisal_ast);
    let ou = To_if1_.do_compilation_unit sisal_ast in
    print_endline "Result graph";
    print_endline (If1.string_of_graph ou);
(*    print_endline (Ast.str_compilation_unit sisal_ast); *)
    If1.write_dot_file ou
  with e ->
    let msg = Printexc.to_string e and stack = Printexc.get_backtrace () in
    Printf.eprintf "there was an error: %s%s\n" msg stack;
    let msg = "Unexpected: " ^ "\"" ^ Lexing.lexeme lexbuf ^ "\"" in
    error msg lexbuf;
    exit 1

let parsing = Printexc.print main ()
let _ = parsing
