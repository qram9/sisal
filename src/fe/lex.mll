{
open Parse
open Lexing
exception LexErr of string
let error msg start finish =
  Printf.sprintf "(line %d: char %d..%d): %s" start.pos_lnum
    (start.pos_cnum -start.pos_bol) (finish.pos_cnum - finish.pos_bol) msg
(*raise (Error msg)*)
let lex_error lexbuf =
  raise ( LexErr (error (lexeme lexbuf) (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)))
let include_stack = ref []

let return x = fun _ -> x (* returns the value x *)
let get         = Lexing.lexeme
let getchar     = Lexing.lexeme_char
let debug_level = ref 3
let padded_lex_msg level fmt =
  let print_at_level str
    = if !debug_level >= level
    then print_string ("              <Matched" ^ str) in
  Format.ksprintf print_at_level fmt


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
    [ ("AND", ANDKW);
      ("ARRAY",ARRAY);
      ("AS", AS);
      ("AT",AT);
      ("BOOLEAN",BOOLEAN);
      ("CATENATE",CATENATE);
      ("CHAR",CHARACTER);
      ("CHARACTER",CHARACTER);
      ("LONG", LONG_TY);
      ("ULONG", ULONG_TY);
      ("CROSS",CROSS);
      ("DEFINE",DEFINE);
      ("DOT", DOT);
      ("DOUBLE_REAL",DOUBLE_REAL);
      ("DOUBLE",DOUBLE_REAL);
      ("ELSE",ELSE);
      ("ELSEIF",ELSEIF);
      ("END",END);
      ("ERROR",ERROR);
      ("FALSE",FALSE);
      ("FLOAT", REAL);
      ("FORWARD",FORWARD);
      ("GLOBAL",GLOBAL);
      ("GREATEST",GREATEST);
      ("LEAST",LEAST);
      ("IN",IN);
      ("INTEGER",INTEGER);
      ("IS",IS);
      ("INITIAL",INITIAL);
      ("LEFT",LEFT);
      ("REC", REC);
      ("NIL",NIL);
      ("NULL",NULL);
      ("OF",OF);
      ("OLD",OLD);
      ("OTHERWISE",OTHERWISE);
      ("PRODUCT",PRODUCT);
      ("REAL",REAL);
      ("RECORD",RECORD);
      ("REPEAT",REPEAT);
      ("REPLACE",REPLACE);
      ("RETURNS",RETURNS);
      ("RIGHT",RIGHT);
      ("STREAM",STREAM);
      ("SUM",SUM);
      ("TAG",TAG);
      ("THEN",THEN);
      ("TREE",TREE);
      ("TRUE",TRUE);
      ("TYPE",TYPE);
      ("UNION",UNION);
      ("UNLESS",UNLESS);
      ("UNTIL",UNTIL);
      ("USING", USING);
      ("VALUE",VALUE);
      ("WHILE",WHILE);
      ("WHEN",WHEN);
      ("FLOAT2", FLOAT2_TY); 
      ("FLOAT3", FLOAT3_TY); 
      ("FLOAT4", FLOAT4_TY); 
      ("CHAR2", CHAR2_TY);  
      ("CHAR3", CHAR3_TY);  
      ("CHAR4", CHAR4_TY);  
      ("HALF2", HALF2_TY);  
      ("HALF4", HALF4_TY);  
      ("HALF8", HALF8_TY);  
      ("MAT2", MAT2_TY);   
      ("MAT3", MAT3_TY);   
      ("MAT4", MAT4_TY);   
      ("LONG2", LONG2_TY);
      ("ULONG2", ULONG2_TY);
      ("LONG3", LONG3_TY);
      ("ULONG3", ULONG3_TY);
      ("LONG4", LONG4_TY);
      ("ULONG4", ULONG4_TY);
      ("LONG8", LONG8_TY);
      ("ULONG8", ULONG8_TY);
      ("LONG16", LONG16_TY);
      ("ULONG16", ULONG16_TY);
    ]
(* Case-insensitive keyword fragments *)

let predef_fn_table =
  List.fold_left
    (fun last (k,v) -> (KeywordTable.add k v last))
    KeywordTable.empty
    [
      ("ABS",ABS);
      ("ARRAY_ADDH",ARRAY_ADDH);
      ("ARRAY_ADDL",ARRAY_ADDL);
      ("ARRAY_ADJUST",ARRAY_ADJUST);
      ("ARRAY_FILL",ARRAY_FILL);
      ("ARRAY_LIMH",ARRAY_LIMH);
      ("ARRAY_LIML",ARRAY_LIML);
      ("ARRAY_PREFIXSIZE",ARRAY_PREFIXSIZE);
      ("ARRAY_REMH",ARRAY_REMH);
      ("ARRAY_REML",ARRAY_REML);
      ("ARRAY_SETL",ARRAY_SETL);
      ("ARRAY_SIZE",ARRAY_SIZE);
      ("EXP",EXP);
      ("FLOOR",FLOOR);
      ("MAX",MAX);
      ("MIN",MIN);
      ("MOD",MOD);
      ("STREAM_APPEND",STREAM_APPEND);
      ("STREAM_EMPTY",STREAM_EMPTY);
      ("STREAM_FIRST",STREAM_FIRST);
      ("STREAM_PREFIXSIZE",STREAM_PREFIXSIZE);
      ("STREAM_REST",STREAM_REST);
      ("STREAM_SIZE",STREAM_SIZE);
      ("TRUNC",TRUNC);
    ]
}
let digit = ['0'-'9']
let hex = ("0x" | "0X") ( digit | ['a'-'f' 'A'-'F'] )+
let dec = digit+
let exp = ['e' 'E'] ['+' '-']? digit+
let dexp = ['d' 'D'] ['+' '-']? digit+
let flonum = (digit+ '.' digit* | '.' digit+ | digit+) exp
           | digit+ '.' digit*
           | '.' digit+
                        

let alpha = ['a'-'z' 'A'-'Z']
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

let string_chars =  (
  ['a'-'z' 'A'-'Z'
   '0'-'9' '%'
         '^' '&' '*' '/'
         '(' ')' '~'
         '#' '$' '\"'
         '\'' ':' ';'
         '`' '@' '-'
         '_' '+' '='
         '?' '<' '>'
         '|' '{' '}' '[' ']'
         '!' '.' ','
         ' ' '\t' '\r'])

let special_chars =
  ('\\' '\\') | ('\\' '\"') | ('\\' 'b') | ('\\' 'f')
  | ('\\' 'n') | ('\\' 'r') | ('\\' 't') | ('\\')
  | ('\\' ['0'-'9'] ['0'-'9'] ['0'-'9']) (* Octal num *)

let match_char = '\'' ( string_chars
                   | special_chars | ('\\' string_chars )) '\''

let match_string = ( string_chars
                   | special_chars | ('\\' string_chars ))+

rule read_comment = parse
                 | '\n' { Lexing.new_line lexbuf; sisal_lex lexbuf }
                 | eof  { EOF }
                 | _    { read_comment lexbuf }

and
  read_string buf = parse

                  | '\"'       { STRING buf }  (* Return the token with the buffer *)
                  | '\\' '\"'  { read_string (buf ^ "\"") lexbuf } (* Handle escaped quote *)
                  | '\\' 'n'   { read_string (buf ^ "\n") lexbuf } (* Handle escaped newline *)
                  | [^ '\"' '\\']+ as text { read_string (buf ^ text) lexbuf } (* Normal text *)
                  | eof        { raise (LexErr "String not terminated") }
                  | _          { raise (LexErr "Illegal character in string") }

and sisal_lex = parse eof {
    EOF
  }
 (* --- 1. Literal Suffixes --- *)
 | digit+ ['l' 'L'] as lxm { LONG(Int64.of_string (String.sub lxm 0 (String.length lxm - 1))) }

 (* ULONG: Strictly positive (Unsigned) *)
 | (digit+ | hex) (['u' 'U'] ['l' 'L'] | ['l' 'L'] ['u' 'U']) as lxm
   { ULONG(Int64.of_string (String.sub lxm 0 (String.length lxm - 2))) }
(* 1. Scientific Double (Mandatory d/D exponent: -1.0d0, 12d5) *)
 | (digit+ ('.' digit*)? | '.' digit+) dexp as lxm
   { 
     let sanitized = String.map (function 'd'|'D' -> 'e' | c -> c) lxm in
     DOUBLE(float_of_string sanitized) 
   }

 (* 2. Suffix-based Float/Half (e.g., 1.2f, 123f, 1.2e5f) *)
 | (digit+ ('.' digit*)? | '.' digit+) exp? ['f' 'F'] as lxm
   { FLOAT(float_of_string (String.sub lxm 0 (String.length lxm - 1))) }

 | (digit+ ('.' digit*)? | '.' digit+) exp? ['h' 'H'] as lxm
   { HALF(float_of_string (String.sub lxm 0 (String.length lxm - 1))) }

 (* 3. Standard Scientific & Floating Point (MUST be above dec) *)
 | flonum as f {
     padded_lex_msg 5 ": %s>\n" f;
     FLOAT (float_of_string f)
   }

 (* 4. Integers (The "Fallthrough" for numbers) *)
 | dec as d {
     padded_lex_msg 5 ": %s>\n" d;
     INT (int_of_string d)
   }
| '%' {
     padded_lex_msg 5 "_cmts:>\n";
     read_comment lexbuf
   }
 | '\"' { 
     padded_lex_msg 5 "_string: starting recursive read...>\n";
     read_string "" lexbuf 
   }
 | match_char as ch
   {
     padded_lex_msg 5 "_char: %s>\n" ch;
     CHAR ch
   }
 | ([' ' '\t'])+ as spaces {
     padded_lex_msg 5 "bunch of spaces: %d>\n" (String.length spaces);
     sisal_lex lexbuf
   }
 | ('\n')  as mynewlines {
     padded_lex_msg 5 ": newline %c>\n" mynewlines;
     Lexing.new_line lexbuf;
     sisal_lex lexbuf
   }
 | "INCLUDE" { 
     padded_lex_msg 5 "_include_start:>\n";
     (* Use our 'Bucket' worker to get the filename! *)
     match read_string "" lexbuf with
     | STRING file -> 
       let chan = open_in file in
       let new_lb = Lexing.from_channel chan in
       (* Tell the new belt its name for error messages *)
       new_lb.lex_curr_p <- { new_lb.lex_curr_p with pos_fname = file };
       include_stack := (lexbuf, chan) :: !include_stack;
       sisal_lex new_lb (* Teleport! *)
     | _ -> lex_error lexbuf
   }
(* 🚀 FUSED MULTI-WORD KEYWORDS *)
  | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['F' 'f'] ['U' 'u'] ['N' 'n'] ['C' 'c'] ['T' 't'] ['I' 'i'] ['O' 'o'] ['N' 'n'] { END_FUNCTION }
  | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['L' 'l'] ['E' 'e'] ['T' 't'] { END_LET }
  | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['F' 'f'] ['O' 'o'] ['R' 'r']{ END_FOR }
  | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+ ['I' 'i'] ['F' 'f'] { END_IF }
  | ['E' 'e'] ['N' 'n'] ['D' 'd'] [' ' '\t' '\n' '\r']+  ['T' 't'] ['A' 'a']['G' 'g'] ['C' 'c'] ['A' 'a'] ['S' 's'] ['E' 'e'] { END_TAGCASE }

              | ['F' 'f'] ['U' 'u'] ['N' 'n'] ['C' 'c'] ['T' 't'] ['I' 'i'] ['O' 'o'] ['N' 'n'] { FUNCTION }
| ['L' 'l'] ['E' 'e'] ['T' 't'] { LET }
              | ['F' 'f'] ['O' 'o'] ['R' 'r']{ FOR }
              |['I' 'i'] ['F' 'f'] { IF }
              | ['T' 't'] ['A' 'a']['G' 'g'] ['C' 'c'] ['A' 'a'] ['S' 's'] ['E' 'e'] { TAGCASE }

 | id as ident_or_kw {
     let lookup_name = String.uppercase_ascii ident_or_kw in
     try
       (* 1. Check the primary keyword table (IF, LET, etc.) *)
       let k = KeywordTable.find lookup_name keyword_table in
       padded_lex_msg 5 ": Keyword:%s>\n" lookup_name;
       k
     with Not_found ->
       (* 2. It's a user-defined variable name *)
       padded_lex_msg 5 ": NAME:%s>\n" lookup_name;
       NAME lookup_name
   }
 | ',' {padded_lex_msg 5 " , >\n"; COMMA}
 | '"' ([^ '"']* as s) '"' { STRING s }
 | '.' {padded_lex_msg 5 " . >\n"; DOTSTOP}
 | "<=" {padded_lex_msg 5 " <=\n"; LE}
 | "<" {padded_lex_msg 5 " <=\n"; LT}
 | ">=" {padded_lex_msg 5 " <=\n"; GE}
 | ">" {padded_lex_msg 5 " <=\n"; GT}
 | "<<" {padded_lex_msg 5 " << >\n"; SHL}
 | ">>" {padded_lex_msg 5 " >> >\n"; SHR}
 | '*' {padded_lex_msg 5 " * >\n"; STAR}
 | '/'  {padded_lex_msg 5 " / >\n"; DIVIDE}
 | '+' {padded_lex_msg 5 " + >\n"; PLUS}
 | '-' {padded_lex_msg 5 " - >\n"; MINUS}
 | "#(" {padded_lex_msg 5 " ( >\n"; HASH_LPAREN}
 | '(' {padded_lex_msg 5 " ( >\n"; LPAREN}
 | ')' {padded_lex_msg 5 " ) >\n"; RPAREN}
 | '[' {padded_lex_msg 5 " [ >\n"; LBRACK}
 | ']' {padded_lex_msg 5 " ] >\n"; RBRACK}
 | '=' {padded_lex_msg 5 " ] >\n"; EQ}
 | ":=" {padded_lex_msg 5 " := >\n"; ASSIGN}
 | ':' {padded_lex_msg 5 " : >\n"; COLON}
 | "||" {padded_lex_msg 5 " || >\n"; PIPE}
 | '|' {padded_lex_msg 5 " | >\n"; OR}
 | "~=" {padded_lex_msg 5 " ~ >\n"; NE}
 | '~' {padded_lex_msg 5 " ~ >\n"; NOT}
 | '&' {padded_lex_msg 5 " & >\n"; AND}
 | [';'] {
  padded_lex_msg 5 " ; >\n";
  SEMICOLON
} | _ {  lex_error lexbuf }
{
  let get_lex_buf = Lexing.from_channel stdin
}
