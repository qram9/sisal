{
open Parse
open Lexing
exception LexErr of string

let error msg start finish =
  Printf.sprintf "(line %d: char %d..%d): %s" start.pos_lnum
    (start.pos_cnum - start.pos_bol) (finish.pos_cnum - finish.pos_bol) msg

let lex_error lexbuf =
  raise (LexErr (error (lexeme lexbuf) (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)))

let include_stack : (Lexing.lexbuf * in_channel * string) list ref = ref []

let return x = fun _ -> x
let get         = Lexing.lexeme
let getchar     = Lexing.lexeme_char
let lex_msg lvl fmt = Ir.Debug.msg "lex" lvl fmt

module KeywordTable =
  Map.Make(struct
    type t = string
    let compare a b =
      String.(compare (lowercase_ascii a) (lowercase_ascii b))
  end)

let keyword_table =
  List.fold_left
    (fun last (k,v) -> (KeywordTable.add k v last))
    KeywordTable.empty
    [ ("AND", ANDKW); ("ARRAY_DV",ARRAY_DV); ("array_dv",ARRAY_DV); ("ARRAY",ARRAY); ("AS", AS); ("AT",AT);
      ("BOOLEAN",BOOLEAN); ("CATENATE",CATENATE); ("CHAR",CHARACTER);
      ("CHARACTER",CHARACTER); ("LONG", LONG_TY); ("ULONG", ULONG_TY);
      ("CROSS",CROSS); ("DEFINE",DEFINE); ("DOT", DOT);
      ("DOUBLE_REAL",DOUBLE_REAL); ("DOUBLE",DOUBLE_REAL);
      ("ELSE",ELSE); ("ELSEIF",ELSEIF);
      ("ERROR",ERROR); ("FALSE",FALSE); ("FLOAT", REAL);
      ("FORWARD",FORWARD); ("GLOBAL",GLOBAL); ("GREATEST",GREATEST);
      ("LEAST",LEAST); ("IN",IN); ("INTEGER",INTEGER);
      ("IS",IS); ("INITIAL",INITIAL); ("LEFT",LEFT);
      ("REC", REC); ("NIL",NIL); ("NULL",NULL);
      ("OF",OF); ("OLD",OLD); ("OTHERWISE",OTHERWISE);
      ("PRODUCT",PRODUCT); ("REAL",REAL); ("RECORD",RECORD);
      ("REPEAT",REPEAT); ("REPLACE",REPLACE); ("RETURNS",RETURNS);
      ("RIGHT",RIGHT); ("STREAM",STREAM); ("SUM",SUM);
      ("TAG",TAG); ("THEN",THEN); ("TREE",TREE);
      ("TRUE",TRUE); ("TUPLE",TUPLE); ("TYPE",TYPE); ("UNION",UNION);
      ("UNLESS",UNLESS); ("UNTIL",UNTIL); ("USING", USING);
      ("VALUE",VALUE); ("WHILE",WHILE); ("WHEN",WHEN);
      ("FLOAT2", FLOAT2_TY); ("FLOAT3", FLOAT3_TY); ("FLOAT4", FLOAT4_TY); 
      ("CHAR2", CHAR2_TY);   ("CHAR3", CHAR3_TY);   ("CHAR4", CHAR4_TY);  
      ("HALF2", HALF2_TY);   ("HALF4", HALF4_TY);   ("HALF8", HALF8_TY);  
      ("MAT2", MAT2_TY);     ("MAT3", MAT3_TY);     ("MAT4", MAT4_TY);   
      ("LONG2", LONG2_TY);   ("ULONG2", ULONG2_TY); ("LONG3", LONG3_TY);
      ("ULONG3", ULONG3_TY); ("LONG4", LONG4_TY);   ("ULONG4", ULONG4_TY);
      ("LONG8", LONG8_TY);   ("ULONG8", ULONG8_TY); ("LONG16", LONG16_TY);
      ("ULONG16", ULONG16_TY); ]

let predef_fn_table =
  (* These are predefined functions / APL bulk operations.  They are NOT in
     keyword_table so they tokenise as NAME (case-insensitive via
     String.uppercase_ascii in the identifier rule).  This lets them be used
     as user-defined identifiers in old Sisal programs while still being
     dispatchable by name in do_simple_exp_impl. *)
  List.fold_left
    (fun last (k,v) -> (KeywordTable.add k v last))
    KeywordTable.empty
    [ ("ABS",ABS); ("ARRAY_ADDH",ARRAY_ADDH); ("ARRAY_ADDL",ARRAY_ADDL);
      ("ARRAY_ADJUST",ARRAY_ADJUST); ("ARRAY_FILL",ARRAY_FILL);
      ("ARRAY_LIMH",ARRAY_LIMH); ("ARRAY_LIML",ARRAY_LIML);
      ("ARRAY_PREFIXSIZE",ARRAY_PREFIXSIZE); ("ARRAY_REMH",ARRAY_REMH);
      ("ARRAY_REML",ARRAY_REML); ("ARRAY_SETL",ARRAY_SETL);
      ("ARRAY_SIZE",ARRAY_SIZE); ("EXP",EXP); ("FLOOR",FLOOR);
      ("MAX",MAX); ("MIN",MIN); ("MOD",MOD);
      ("STREAM_APPEND",STREAM_APPEND); ("STREAM_EMPTY",STREAM_EMPTY);
      ("STREAM_FIRST",STREAM_FIRST); ("STREAM_PREFIXSIZE",STREAM_PREFIXSIZE);
      ("STREAM_REST",STREAM_REST); ("STREAM_SIZE",STREAM_SIZE);
      ("TRUNC",TRUNC);
      (* APL bulk ops are NOT in keyword_table — they arrive as NAME tokens
         (case-insensitive via String.uppercase_ascii) and are dispatched in
         do_simple_exp_impl by string match.  Names: MAP/EACH/APPLY, FOLDL,
         FOLDR, SCAN, TAKE, DROP, ROTATE, REVERSE, COMPRESS, OUTERPRODUCT,
         SORT, GRADE_UP/ARGSORT, GRADE_DOWN, ARGMAX, ARGMIN, NONZERO, WHERE,
         MEAN, VARIANCE, STDDEV, ANY, ALL, NORM, CUMSUM, CUMPROD, CONCAT/
         CATENATE_OP, TILE, SQUEEZE, EXPAND, RAVEL/FLATTEN_DV, STENCIL, PAD,
         INNERPRODUCT, RESHAPE, PERMUTE. *) ]
}

let digit = ['0'-'9']
let hex = ("0x" | "0X") ( digit | ['a'-'f' 'A'-'F'] )+
let dec = digit+
let exp = ['e' 'E'] ['+' '-']? digit+
let dexp = ['d' 'D'] ['+' '-']? digit+
let flonum = (digit+ '.' digit* | '.' digit+ | digit+) exp
           | digit+ '.' digit*
           | '.' digit+
                        
let inc_kw = ['i' 'I'] ['n' 'N'] ['c' 'C'] ['l' 'L'] ['u' 'U'] ['d' 'D'] ['e' 'E']

let alpha = ['a'-'z' 'A'-'Z']
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

let string_chars =  (
  ['a'-'z' 'A'-'Z' '0'-'9' '%' '^' '&' '*' '/' '(' ')' '~' '#' '$' '\"'
   '\'' ':' ';' '`' '@' '-' '_' '+' '=' '?' '<' '>' '|' '{' '}' '[' ']'
   '!' '.' ',' ' ' '\t' '\r'])
let ws = [' ' '\t']*

let special_chars =
  ('\\' '\\') | ('\\' '\"') | ('\\' 'b') | ('\\' 'f')
  | ('\\' 'n') | ('\\' 'r') | ('\\' 't') | ('\\')
  | ('\\' ['0'-'9'] ['0'-'9'] ['0'-'9'])

let match_char = '\'' ( string_chars | special_chars | ('\\' string_chars )) '\''

(* CRITICAL CHANGE 1: Internal rules now call 'internal_lex', not 'sisal_lex' 
*)
rule read_comment = parse
  | '\n' { Lexing.new_line lexbuf; internal_lex lexbuf }
  | eof  { internal_lex lexbuf } 
  | _    { read_comment lexbuf }

and read_string buf = parse
  | '\"'       { STRING buf } 
  | '\\' '\"'  { read_string (buf ^ "\"") lexbuf } 
  | '\\' 'n'   { read_string (buf ^ "\n") lexbuf } 
  | [^ '\"' '\\']+ as text { read_string (buf ^ text) lexbuf } 
  | eof        { raise (LexErr "String not terminated") }
  | _          { raise (LexErr "Illegal character in string") }

and internal_lex = parse 
  | eof { EOF }

 (* --- 1. Literal Suffixes --- *)
 | digit+ ['l' 'L'] as lxm { LONG(Int64.of_string (String.sub lxm 0 (String.length lxm - 1))) }

 | (digit+ | hex) (['u' 'U'] ['l' 'L'] | ['l' 'L'] ['u' 'U']) as lxm
   { ULONG(Int64.of_string (String.sub lxm 0 (String.length lxm - 2))) }

 | (digit+ ('.' digit*)? | '.' digit+) dexp as lxm
   { 
     let sanitized = String.map (function 'd'|'D' -> 'e' | c -> c) lxm in
     DOUBLE(float_of_string sanitized) 
   }

 | (digit+ ('.' digit*)? | '.' digit+) exp? ['f' 'F'] as lxm
   { FLOAT(float_of_string (String.sub lxm 0 (String.length lxm - 1))) }

 | (digit+ ('.' digit*)? | '.' digit+) exp? ['h' 'H'] as lxm
   { HALF(float_of_string (String.sub lxm 0 (String.length lxm - 1))) }

 (* 3. Standard Scientific & Floating Point *)
 | flonum as f {
     lex_msg 5 ": %s" f;
     FLOAT (float_of_string f)
   }

 (* 4. Integers *)
 | dec as d {
     lex_msg 5 ": %s" d;
     INT (int_of_string d)
   }

 (* 5. Include Directive *)
 | "%$" ws inc_kw ws '('? ws '"' ([^ '"' '\n']+ as file) '"' ws ')'? [^ '\n']*
      {
        (* Resolve relative includes against the current file's directory *)
        let cur_file = lexbuf.lex_curr_p.pos_fname in
        let resolved =
          if Filename.is_relative file then
            let dir = Filename.dirname cur_file in
            if dir = "." then file else Filename.concat dir file
          else file
        in
        if List.exists (fun (_, _, f) -> f = resolved) !include_stack then begin
          Printf.eprintf "Error: Cyclic include detected: '%s' is already being included\n" resolved;
          internal_lex lexbuf
        end else
        try
          let chan = open_in resolved in
          let new_lb = Lexing.from_channel chan in
          new_lb.lex_curr_p <- { new_lb.lex_curr_p with pos_fname = resolved };
          include_stack := (new_lb, chan, resolved) :: !include_stack;
          lex_msg 5 "_include_start:";
          internal_lex new_lb
        with Sys_error msg ->
          Printf.eprintf "Warning: Could not include '%s': %s\n" resolved msg;
          internal_lex lexbuf
      }

 (* 6. Comments *)
 | '%' {
     lex_msg 5 "_cmts:";
     read_comment lexbuf
   }

 (* 7. Strings and Chars *)
 | '\"' { 
     lex_msg 5 "_string: starting recursive read...";
     read_string "" lexbuf 
   }
 | match_char as ch {
     lex_msg 5 "_char: %s" ch;
     CHAR ch
   }

 (* 8. Whitespace *)
 | ([' ' '\t'])+ as spaces {
     lex_msg 5 "bunch of spaces: %d" (String.length spaces);
     internal_lex lexbuf
   }
 | ('\n')  as mynewlines {
     lex_msg 5 ": newline %c" mynewlines;
     Lexing.new_line lexbuf;
     internal_lex lexbuf
   }

 (* 9. FUSED MULTI-WORD KEYWORDS *)
 | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['F' 'f'] ['U' 'u'] ['N' 'n'] ['C' 'c'] ['T' 't'] ['I' 'i'] ['O' 'o'] ['N' 'n'] { END_FUNCTION }
 | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['L' 'l'] ['E' 'e'] ['T' 't'] { END_LET }
 | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['F' 'f'] ['O' 'o'] ['R' 'r']{ END_FOR }
 | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['I' 'i'] ['F' 'f'] { END_IF }
 | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+  ['T' 't'] ['A' 'a']['G' 'g'] ['C' 'c'] ['A' 'a'] ['S' 's'] ['E' 'e'] { END_TAGCASE }
 
 | ['F' 'f'] ['U' 'u'] ['N' 'n'] ['C' 'c'] ['T' 't'] ['I' 'i'] ['O' 'o'] ['N' 'n'] { FUNCTION }
 | ['L' 'l'] ['E' 'e'] ['T' 't'] { LET }
 | ['F' 'f'] ['O' 'o'] ['R' 'r']{ FOR }
 | ['I' 'i'] ['F' 'f'] { IF }
 | ['T' 't'] ['A' 'a']['G' 'g'] ['C' 'c'] ['A' 'a'] ['S' 's'] ['E' 'e'] { TAGCASE }

 (* 10. Identifiers / Single-Word Keywords *)
 | id as ident_or_kw {
     let lookup_name = String.uppercase_ascii ident_or_kw in
     try
       let k = KeywordTable.find lookup_name keyword_table in
       lex_msg 5 ": Keyword:%s" lookup_name;
       k
     with Not_found ->
       lex_msg 5 ": NAME:%s" lookup_name;
       NAME lookup_name
   }

 (* 11. Symbols & Operators *)
 | ',' {lex_msg 5 " , "; COMMA}
 | ".." {lex_msg 5 " .. "; DOTDOT}
 | '.' {lex_msg 5 " . "; DOTSTOP}
 | "<=" {lex_msg 5 " <=\n"; LE}
 | "<" {lex_msg 5 " <=\n"; LT}
 | ">=" {lex_msg 5 " <=\n"; GE}
 | ">" {lex_msg 5 " <=\n"; GT}
 | "<<" {lex_msg 5 " << "; SHL}
 | ">>" {lex_msg 5 " >> "; SHR}
 | '*' {lex_msg 5 " * "; STAR}
 | '/'  {lex_msg 5 " / "; DIVIDE}
 | '+' {lex_msg 5 " + "; PLUS}
 | '-' {lex_msg 5 " - "; MINUS}
 | "#(" {lex_msg 5 " ( "; HASH_LPAREN}
 | '(' {lex_msg 5 " ( "; LPAREN}
 | ')' {lex_msg 5 " ) "; RPAREN}
 | '[' {lex_msg 5 " [ "; LBRACK}
 | ']' {lex_msg 5 " ] "; RBRACK}
 | '=' {lex_msg 5 " ] "; EQ}
 | ":=" {lex_msg 5 " := "; ASSIGN}
 | ':' {lex_msg 5 " : "; COLON}
 | "||" {lex_msg 5 " || "; PIPE}
 | '|' {lex_msg 5 " | "; OR}
 | "~=" {lex_msg 5 " ~ "; NE}
 | '~' {lex_msg 5 " ~ "; NOT}
 | '&' {lex_msg 5 " & "; AND}
 | [';'] {
  lex_msg 5 " ; ";
  SEMICOLON
 } 
 | _ { lex_error lexbuf }

{
  (* CRITICAL CHANGE 2: The Interceptor Wrapper
    This sits between parse.mly and internal_lex. When parse.mly blindly
    asks for a token from the main lexbuf, this wrapper intercepts it and 
    silently forces it to read from the include_stack instead.
  *)
  let rec sisal_lex original_lexbuf =
    let active_lexbuf =
      match !include_stack with
      | (lb, _, _) :: _ -> lb
      | [] -> original_lexbuf
    in
    
    let tok = internal_lex active_lexbuf in
    
    if tok = EOF && !include_stack <> [] then begin
       match !include_stack with
       | (_, chan, _) :: rest ->
           close_in chan;
           include_stack := rest;
           lex_msg 5 "_include_end:<\n";
           
           (* Included file is done. Immediately fetch the next token 
              from the parent file to keep the parser happy. *)
           sisal_lex original_lexbuf
       | [] -> assert false
    end else
       tok

  let get_lex_buf = Lexing.from_channel stdin
}
