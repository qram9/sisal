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
  let rec parse = function
    | [] -> ()
    | "--ast" :: rest ->
        ast_dest := Stdout; parse rest
    | a :: rest when String.length a > 6 && String.sub a 0 6 = "--ast=" ->
        ast_dest := File (String.sub a 6 (String.length a - 6)); parse rest
    | "--if1" :: rest ->
        if1_dest := Stdout; parse rest
    | a :: rest when String.length a > 6 && String.sub a 0 6 = "--if1=" ->
        if1_dest := File (String.sub a 6 (String.length a - 6)); parse rest
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
        let (Ast.Compilation_unit frags) = Parse.main Lex.sisal_lex lb in
        frags
      end else
        List.concat_map (fun fname ->
          let lb = Lexing.from_channel (open_in fname) in
          let lb = set_filename fname lb in
          last_lexbuf := lb;
          let (Ast.Compilation_unit frags) = Parse.main Lex.sisal_lex lb in
          frags
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
    | _ ->
        let msg = "Unexpected: " ^ "\"" ^ Lexing.lexeme lexbuf ^ "\"" in
        error msg lexbuf);
    exit 1

let parsing = Printexc.print main ()
let _ = parsing
