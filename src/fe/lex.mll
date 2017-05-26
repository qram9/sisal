{
open Parse
exception Error of string
let error msg = raise (Error msg)
let return x = fun map -> x (* returns the value x *)
let get         = Lexing.lexeme
let getchar     = Lexing.lexeme_char
let debug_level = ref 5
let padded_lex_msg level fmt = 
  let print_at_level str 
    = if !debug_level >= level 
    then print_string ("              <Matched" ^ str) in
  Format.ksprintf print_at_level fmt

let rec mycou strin last pres cou =
  (match compare pres last with
   | 0 -> cou
   | _ -> (match compare (String.get strin pres) '\n' with 
       | 0 -> mycou strin last (pres+1) (cou+1)
       | _ -> mycou strin last (pres+1) cou)) 

module KeywordTable =
  Map.Make(struct
    type t = string
    let compare a b =
      String.(compare (lowercase a) (lowercase b))
  end)

let keyword_table =
  List.fold_left
    (fun last (k,v) -> (KeywordTable.add k v last))
    KeywordTable.empty
    [ ("ARRAY",ARRAY);
      ("AT",AT);
      ("BOOLEAN",BOOLEAN);
      ("CATENATE",CATENATE);
      ("CHARACTER",CHARACTER);
      ("CROSS",CROSS);
      ("DEFINE",DEFINE);
      ("DOT",DOT);
      ("DOUBLE_REAL",DOUBLE_REAL);
      ("ELSE",ELSE);
      ("ELSEIF",ELSEIF);
      ("END",END);
      ("ERROR",ERROR);
      ("FALSE",FALSE);
      ("FOR",FOR);
      ("FORWARD",FORWARD);
      ("FUNCTION",FUNCTION);
      ("GLOBAL",GLOBAL);
      ("GREATEST",GREATEST);
      ("IF",IF);
      ("IN",IN);
      ("INTEGER",INTEGER);
      ("IS",IS);
      ("INITIAL",INITIAL);
      ("LEFT",LEFT);
      ("LET",LET);
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
      ("TAGCASE",TAGCASE);
      ("THEN",THEN);
      ("TREE",TREE);
      ("TRUE",TRUE);
      ("TYPE",TYPE);
      ("UNION",UNION);
      ("UNLESS",UNLESS);
      ("UNTIL",UNTIL);
      ("VALUE",VALUE);
      ("WHILE",WHILE);
      ("WHEN",WHEN);
    ]

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
let flonum = (['+' '-']?) ['0'-'9']+ 
             '.' 
             ['0'-'9']*
             (['e' 'E']?
             ['+' '-']?
             ['0'-'9']+)*

                                 let negnum = '-'? dec
let negflonum = '-'? flonum

let alpha = ['a'-'z' 'A'-'Z']
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']* 
         let match_char = '\'' ['a'-'z'] '\''

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

let match_string = ( string_chars 
                   | special_chars | ('\\' string_chars ))+ 

rule sisal_lex = parse eof { 
  EOF
}
| '%' (match_string)? {
  padded_lex_msg 5 "_cmts:>\n"; 
  sisal_lex lexbuf
  }
| '\"' (match_string as st) '\"' 
{
  padded_lex_msg 5 "_string: %s>\n" st; 
  print_endline st;
  STRING st
}
| match_char as ch 
{
  padded_lex_msg 5 "_char: %s>\n" ch; 
  print_endline ch;
  CHAR ch 
}
| ([' ' '\t'])+ as spaces {
  padded_lex_msg 5 "bunch of spaces: %d>\n" (String.length spaces);
  sisal_lex lexbuf
}
| ('\n')+  as mynewlines {
  padded_lex_msg 5 ": EOL:%d times>\n" (String.length mynewlines);
  print_endline "\n";
  (*Lexing.new_line lexbuf;*)sisal_lex lexbuf
}
| flonum as f {
  padded_lex_msg 5 ": %s>\n" f;
  print_endline "\n";
  FLOAT (float_of_string f)
}
| dec as d {
  padded_lex_msg 5 ": %s>\n" d;
  print_endline "\n";
  INT (int_of_string d)
}
| id+ as ident_or_kw {
  try
    let k = 
    KeywordTable.find ident_or_kw keyword_table
    in padded_lex_msg 5 ": Keyword:%s>\n" (String.uppercase ident_or_kw);
    k
  with Not_found ->
    try
      let k =
        KeywordTable.find ident_or_kw predef_fn_table
      in padded_lex_msg 5 ": Predef_fn:%s>\n" (String.uppercase ident_or_kw);
      (*k*)
      NAME (String.uppercase ident_or_kw)
    with Not_found ->
      padded_lex_msg 5 ": NAME:%s>\n" (String.uppercase ident_or_kw);
      NAME (String.uppercase ident_or_kw)
}
| ',' {padded_lex_msg 5 " , >\n"; COMMA}
| '.' {padded_lex_msg 5 " . >\n"; DOTSTOP}
| "<=" {padded_lex_msg 5 " <=\n"; LE}
| "<" {padded_lex_msg 5 " <=\n"; LT}
| ">=" {padded_lex_msg 5 " <=\n"; GE}
| ">" {padded_lex_msg 5 " <=\n"; GT}
| "<<" {padded_lex_msg 5 " << >\n"; SHL}
| ">>" {padded_lex_msg 5 " >> >\n"; SHR}
| '*' {padded_lex_msg 5 " * >\n"; STAR}
| '+' {padded_lex_msg 5 " + >\n"; PLUS}
| '-' {padded_lex_msg 5 " - >\n"; MINUS}
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
}
{
  let get_lex_buf = Lexing.from_channel stdin
}
