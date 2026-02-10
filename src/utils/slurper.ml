module Parse = Fe.Parse
module Lex = Fe.Lex

let slurp_file filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  (* We use Fe.Parse directly because Utils depends on Fe *)
  let ubit = Parse.main Lex.sisal_lex lexbuf in
  close_in chan;
  ubit
