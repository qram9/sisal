module Lex = Fe.Lex
open Lexing
module Parse = Fe.Parse
module I = Parse.MenhirInterpreter
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

(* Incremental parse with error-state message lookup *)
let rec parse_loop lexbuf checkpoint =
  match checkpoint with
  | I.InputNeeded _ ->
      let token = Lex.sisal_lex lexbuf in
      let s = lexbuf.lex_start_p and e = lexbuf.lex_curr_p in
      parse_loop lexbuf (I.offer checkpoint (token, s, e))
  | I.Shifting _ | I.AboutToReduce _ ->
      parse_loop lexbuf (I.resume checkpoint)
  | I.HandlingError env ->
      let state = I.current_state_number env in
      let msg =
        (try String.trim (Fe.Parse_errors.message state)
         with Not_found -> "syntax error")
      in
      let pos = lexbuf.lex_start_p in
      Printf.eprintf "Parse error in %s, line %d, col %d:\n  %s\n"
        pos.pos_fname pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol)
        msg;
      exit 1
  | I.Accepted v -> v
  | I.Rejected ->
      Printf.eprintf "Parse error: parser rejected input\n";
      exit 1

let parse_lexbuf lexbuf =
  let (Ast.Compilation_unit frags) =
    parse_loop lexbuf (Parse.Incremental.main lexbuf.lex_curr_p)
  in
  frags

(* None = not requested, Some None = stdout, Some (Some f) = file f *)
type out_dest = Nothing | Stdout | File of string

let write_to dest content =
  match dest with
  | Nothing -> ()
  | Stdout -> print_string content
  | File f ->
      let oc = open_out f in
      output_string oc content;
      close_out oc

let default_if1_name files =
  match files with
  | [] -> "out.if1"
  | f :: _ -> Filename.remove_extension f ^ ".if1"

let main () =
  let args = Array.to_list Sys.argv |> List.tl in
  (* Strip --debug=N *)
  let args = List.filter (fun a ->
    if String.length a > 8 && String.sub a 0 8 = "--debug=" then begin
      Ir.Debug.level := int_of_string (String.sub a 8 (String.length a - 8)); false
    end else true) args in
  (* Parse flags *)
  let ast_dest  = ref Nothing in
  let if1_dest  = ref Nothing in
  let files     = ref [] in
  let usage () =
    print_string
      ("Usage: main.exe [OPTIONS] [FILE...]\n\n\
        Options:\n\
        \  --ast            Print AST to stdout\n\
        \  --ast=FILE       Write AST to FILE\n\
        \  --if1            Print IF1 to stdout\n\
        \  --if1=FILE       Write IF1 to FILE\n\
        \  --debug=N        Set debug verbosity level to N\n\
        \  --help           Show this help and exit\n\n\
        If no FILE is given, reads from stdin.\n\
        If neither --ast nor --if1 is given, IF1 is written to <input>.if1.\n");
    exit 0
  in
  let rec parse = function
    | [] -> ()
    | "--help" :: _ -> usage ()
    | "--ast" :: rest ->
        ast_dest := Stdout; parse rest
    | a :: rest when String.length a > 6 && String.sub a 0 6 = "--ast=" ->
        ast_dest := File (String.sub a 6 (String.length a - 6)); parse rest
    | "--if1" :: rest ->
        if1_dest := Stdout; parse rest
    | a :: rest when String.length a > 6 && String.sub a 0 6 = "--if1=" ->
        if1_dest := File (String.sub a 6 (String.length a - 6)); parse rest
    | a :: _ when String.length a > 2 && String.sub a 0 2 = "--" ->
        Printf.eprintf "Unknown option: %s\nTry --help for usage.\n" a; exit 1
    | f :: rest ->
        files := !files @ [f]; parse rest
  in
  parse args;
  (* Default: write IF1 to file derived from first source *)
  if !ast_dest = Nothing && !if1_dest = Nothing then
    if1_dest := File (default_if1_name !files);
  let set_filename (fname : string) (lexbuf : Lexing.lexbuf) =
    lexbuf.Lexing.lex_curr_p <-
      { lexbuf.lex_curr_p with Lexing.pos_fname = fname };
    lexbuf
  in
  let last_lexbuf = ref Lex.get_lex_buf in
  try
    let all_fragments =
      if !files = [] then begin
        let lb = set_filename "<stdin>" Lex.get_lex_buf in
        last_lexbuf := lb;
        parse_lexbuf lb
      end else
        List.concat_map (fun fname ->
          let lb = Lexing.from_channel (open_in fname) in
          let lb = set_filename fname lb in
          last_lexbuf := lb;
          parse_lexbuf lb
        ) !files
    in
    let sisal_ast = Ast.Compilation_unit all_fragments in
    write_to !ast_dest (Ast.str_compilation_unit sisal_ast ^ "\n");
    let ou = To_if1_.do_compilation_unit sisal_ast in
    If1.If1_View.export_debug_html "compiler_dump.html" ou;
    write_to !if1_dest (If1.string_of_graph_thin ou ^ "\n");
    If1.write_dot_file ou
  with e ->
    let msg = Printexc.to_string e and stack = Printexc.get_backtrace () in
    Printf.eprintf "there was an error: %s%s\n" msg stack;
    let lexbuf = !last_lexbuf in
    (match e with
    | Ir.If1.Sem_error _ | Ir.If1.Node_not_found _ ->
        let line, col = !To_if1_.current_src_pos in
        if line > 0 then
          Printf.eprintf "  near line %d, col %d\n" line col
        else begin
          let msg = "Unexpected: " ^ "\"" ^ Lexing.lexeme lexbuf ^ "\"" in
          error msg lexbuf
        end
    | Sys_error msg ->
        Printf.eprintf "%s\n" msg
    | _ ->
        let msg = "Unexpected: " ^ "\"" ^ Lexing.lexeme lexbuf ^ "\"" in
        error msg lexbuf);
    exit 1

let parsing = Printexc.print main ()
let _ = parsing
