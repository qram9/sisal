open Unix
open Lex
open Parse
open Type
exception Error of string
let error msg = raise (Error msg)

let help = 
  [ "usage: sisal_it -help prints this message"
  ; "       sisal_it -debug prints debug messages"
  ]
let main () =
  let lexbuf = 
    if Array.length Sys.argv > 1
    then 
      Lexing.from_channel (open_in Sys.argv.(1))
    else get_lex_buf
  in
  Parse.main Lex.sisal_lex lexbuf
let parsing = Printexc.print main ()
let _ = parsing
