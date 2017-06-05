open Unix
open Lex
open Lexing
open Parse
open Type

let help = 
  [ "usage: sisal_it -help prints this message"
  ; "       sisal_it -debug prints debug messages"
  ]
let error msg lexbuf = 
    let start = (Lexing.lexeme_start_p lexbuf) in
    let finish = (Lexing.lexeme_end_p lexbuf) in
    print_endline (
      Printf.sprintf ("(line %d" ^^ ": char %d" ^^ "..%d)"^^ ": %s") start.pos_lnum 
        (start.pos_cnum -start.pos_bol) (finish.pos_cnum - finish.pos_bol) msg)

let main () =
  let lexbuf = 
    if Array.length Sys.argv > 1
    then 
      Lexing.from_channel (open_in Sys.argv.(1))
    else get_lex_buf
  in
  try
    print_endline (str_compilation_unit (Parse.main Lex.sisal_lex lexbuf));"Done"
  with Parsing.Parse_error ->
    let msg = "Parse error before " ^ (Lexing.lexeme lexbuf) in
    error msg lexbuf;
    exit 1
let parsing = Printexc.print main ()
let _ = parsing

