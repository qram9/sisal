%{
open Type
  let debug_level = ref 3

let parse_msg level fmt = 
  let print_at_level str 
    = if !debug_level >= level 
    then print_string str in
  Format.ksprintf print_at_level fmt
  %}


%token PIPE
%token OR
%token AND
%token NOT
%token LT
%token GT
%token LE
%token GE
%token EQ
%token NE
%token IN
%token ASSIGN
%token COLON
%token DOT
%token DOTSTOP
%token COMMA
%token SEMICOLON
%token LPAREN
%token RPAREN
%token LBRACK
%token RBRACK
%token SHL
%token SHR
%token<string> PREDEF_FN
%token<int> INT
%token<float> FLOAT
%token ARRAY
%token AT
%token BOOLEAN
%token<string> CHAR
%token CHARACTER
%token CROSS
%token DEFINE
%token DOUBLE_REAL
%token INTEGER
%token INITIAL
%token ELSE
%token ELSEIF
%token END
%token ERROR
%token FALSE
%token FOR
%token FORWARD
%token FUNCTION
%token GLOBAL
%token GREATEST
%token<string> NAME
%token IF
%token IS
%token LEAST
%token LEFT
%token LET
%token NIL
%token NULL
%token OF
%token OLD
%token OTHERWISE
%token REAL
%token RECORD
%token REPEAT
%token REPLACE
%token RETURNS
%token RIGHT
%token STREAM
%token SUM
%token TAG
%token TAGCASE
%token THEN
%token TREE
%token TRUE
%token TYPE
%token UNION
%token UNLESS
%token UNTIL
%token VALUE
%token WHILE
%token WHEN
%token CATENATE
%token PRODUCT
%token ABS
%token ARRAY_ADDH
%token ARRAY_ADDL
%token ARRAY_ADJUST
%token ARRAY_FILL
%token ARRAY_LIMH
%token ARRAY_LIML
%token ARRAY_PREFIXSIZE
%token ARRAY_REMH
%token ARRAY_REML
%token ARRAY_SETL
%token ARRAY_SIZE
%token EXP
%token FLOOR
%token MAX
%token MIN
%token MOD
%token STREAM_APPEND
%token STREAM_EMPTY
%token STREAM_FIRST
%token STREAM_PREFIXSIZE
%token STREAM_REST
%token STREAM_SIZE
%token<string> STRING
%token TRUNC
%token EOF
%token PLUS
%token MINUS
%token STAR
%token DIVIDE
%left LT GT EQ NE LE GE PIPE AND OR 
%left PLUS MINUS
%left STAR DIVIDE
%nonassoc UMINUS
%type <string> main
%start main
%%
compilation_unit :
  def_func_name_list function_def_list
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[compilation unit:%s#1]>\n" $1;
      $1 ^ " " ^ $2 
    }
| def_func_name_list type_def_part function_def_list
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[compilation unit:%s#1]>\n" 
      ($1 ^ " " ^ $2 ^ " " ^ $3);
    $1 ^ " " ^ $2 ^ " " ^ $3
  }
| def_func_name_list type_def_part global_header_list function_def_list
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[compilation unit:%s#1]>\n" 
      ($1 ^ " " ^ $2 ^ " " ^ $3 ^ " " ^ $4);
    ($1 ^ " " ^ $2 ^ " " ^ $3 ^ " " ^ $4)
  }
| def_func_name_list type_def_part SEMICOLON function_def_list
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[compilation unit:%s#1]>\n" 
      ($1 ^ " " ^ $2 ^ " " ^ $4);
    $1 ^ " " ^ $2 ^ "; " ^ $4
  }
| def_func_name_list type_def_part  SEMICOLON global_header_list function_def_list
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[compilation unit:%s#1]>\n" 
      ($1 ^ " " ^ $2 ^ "; " ^ $4 ^ " " ^ $5);
    ($1 ^ " " ^ $2 ^ "; " ^ $4 ^ " " ^ $5)
  }

;

global_header_list :
  GLOBAL function_header
    {
        "GLOBAL " ^ $2
    }
| global_header_list GLOBAL function_header
    {
        $1 ^ " " ^ " GLOBAL " ^ $3
    }
;

def_func_name_list:
  DEFINE function_name_list
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[DEFINE_func_name_list:%s#1]>\n"
        ("DEFINE " ^ $2);
      ("DEFINE " ^ $2)
    }
;
function_name_list :
  names
    {
      $1
    }
;
function_def_list: function_def
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[function_list:%s#1]>\n"
        ($1);
      $1
    }
| function_def_list function_def
  {

    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[function_list:%s#2]>\n"
      ($1 ^ " " ^ $2);
    ($1 ^ " " ^ $2)
  }
;

function_def: FORWARD FUNCTION function_header
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[forward function:%s#1]>\n"
        ("FORWARD FUNCTION " ^ $3);
      ("FORWARD FUNCTION " ^ $3)
    }
|      function_def_nest
  {

    $1
  }
;
function_def_nest: function_def_head expression END FUNCTION
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[function_def:%s#1]>\n"
        ("FUNCTION_def " ^ $1 ^ $2 ^ " END FUNCTION");
      ("FUNCTION_def " ^ $1 ^ $2 ^ " END FUNCTION")
    }
| function_def_head function_def_nest expression END FUNCTION
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[function_def:%s#1]>\n"
      ("FUNCTION_def_nested " ^ $1 ^ $2 ^ $3 ^ " END FUNCTION");
    ("FUNCTION_def_nested " ^ $1 ^ $2 ^ $3 ^ " END FUNCTION")
  }
;
function_def_head:
  |   FUNCTION function_header
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[function:%s#1]>\n"
        ("FUNCTION " ^ $2);
      ("FUNCTION " ^ $2)
    }
|   FUNCTION function_header type_def_part SEMICOLON
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[function:%s#1]>\n"
      ("FUNCTION " ^ $2);
    ("FUNCTION " ^ $2)
  }
|   FUNCTION function_header type_def_part
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[function:%s#1]>\n"
      ("FUNCTION " ^ $2);
    ("FUNCTION " ^ $2)
  }
;

function_header : 
  function_name LPAREN RETURNS type_list RPAREN
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[function_header:%s#1]>\n"
        ($1 ^ " ( RETURNS " ^ $4 ^ ")");
      ($1 ^ " ( RETURNS " ^ $4 ^ ")")
    }
| function_name LPAREN decl_list_semi RETURNS type_list RPAREN
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[function_header:%s#1]>\n"
      ($1 ^ " (" ^ $3 ^ " RETURNS " ^ $5 ^ ")");
    ($1 ^ " (" ^ $3 ^ " RETURNS " ^ $5 ^ ")")
  }
;

decl_list_semi:
 decl_list { $1}
| decl_list_semi SEMICOLON decl_list {$1 ^ ";" ^ $3}
;

type_list :
  type_spec
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[type_spec:%s#1]>\n" $1;
      $1
    }
|   type_list COMMA type_spec
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[type_spec:%s#1]>\n" ($1 ^ "," ^ $3);
    ($1 ^ "," ^ $3)
  }
  expression :
      simple_expression
        {
          let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
          parse_msg 5 "<Parsed:[expression:%s#1]>\n" $1;
          $1
        }
|  expression COMMA simple_expression
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[expression comma seperated:%s#1]>\n" $1;
    $1 ^ "," ^ $3
  }
;

simple_expression:
  primary_part2
    {
      "(" ^ $1 ^")"
    }
| simple_expression   GT simple_expression { "(" ^ $1 ^  ">" ^ " " ^ $3 ^ ")" }
| simple_expression   GE simple_expression { "(" ^ $1 ^  ">=" ^ " " ^ $3 ^ ")" }
| simple_expression   LT simple_expression { "(" ^ $1 ^  "<" ^ " " ^ $3 ^ ")" }
| simple_expression   LE simple_expression { "(" ^ $1 ^  "<=" ^ " " ^ $3 ^ ")" }
| simple_expression   EQ simple_expression { "(" ^ $1 ^  "=" ^ " " ^ $3 ^ ")" }
| simple_expression   NE simple_expression { "(" ^ $1 ^  "~=" ^ " " ^ $3 ^ ")" }
| simple_expression   PLUS simple_expression { "(" ^ $1 ^  "+" ^ " " ^ $3 ^ ")" }
| simple_expression   MINUS simple_expression { "(" ^ $1 ^  "-" ^ " " ^ $3 ^ ")" }
| simple_expression   OR simple_expression { "(" ^ $1 ^  "|" ^ " " ^ $3 ^ ")" }
| simple_expression   STAR simple_expression { "(" ^ $1 ^  "*" ^ " " ^ $3 ^ ")" }
| simple_expression   DIVIDE simple_expression { "(" ^ $1 ^  "/" ^ " " ^ $3 ^ ")" }
| simple_expression   AND simple_expression { "(" ^ $1 ^  "&" ^ " " ^ $3 ^ ")" }
| simple_expression   PIPE simple_expression { "(" ^ $1 ^  "||" ^ " " ^ $3 ^ ")" }
|  PLUS simple_expression
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[UNARY_PLUS:%s#1]>\n" ("+" ^ $2);
    ("+" ^ $2)
  }
|   MINUS simple_expression %prec UMINUS
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[UNARY_MINUS:%s#1]>\n" ("-" ^ $2);
    ("-" ^ $2)
  }
|   NOT simple_expression %prec UMINUS
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[UNARY_NOT:%s#1]>\n" ("~" ^ $2);
    ("~" ^ $2)
  }

;

primary_part2 :
  primary
    {
      $1
    }
|    array_ref
  {
    $1
  }
|     array_generator
  {
    $1
  }
|     stream_generator
  {
    $1
  }
|     record_ref
  {
    $1
  }
|     record_generator
  {
    $1
  }
|     union_test
  {
    $1
  }
|     union_generator
  {
    $1
  }
|     error_test
  {
    $1
  }
|     prefix_operation
  {
    $1
  }
|     conditional_exp
  {
    $1
  }
|   let_in_exp
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[let_in_exp#1]>";
    $1
  }
|   tagcase_exp
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[tagcase_exp#1]>";
    $1
  }
|   iteration_exp
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[iteration_exp]>";
    $1
  }
;

tagcase_exp :
  TAGCASE expression tag_list_colon_expression END TAGCASE
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[TAGCASE]#1>:%s\n" ("TAGCASE " ^ $2);
      "TAGCASE " ^ $2 ^ " " ^ $3 ^ " END TAGCASE"
    }
|    TAGCASE expression tag_list_colon_expression 
  OTHERWISE COLON expression END TAGCASE
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[TAGCASE]#2>:%s\n"
      ("TAGCASE " ^ $2 ^ " " ^ $3 ^ " OTHERWISE : " ^ $6 ^ "END TAGCASE");
    "TAGCASE " ^ $2 ^ " " ^ $3 ^ " OTHERWISE : " ^ $6 ^ "END TAGCASE"
  }
| TAGCASE value_name ASSIGN expression tag_list_colon_expression END TAGCASE
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[TAGCASE#3]:%s\n>"
      ("TAGCASE " ^ $2 ^ " := " ^ $4 ^ " " ^ $5 ^ "END TAGCASE");
    "TAGCASE " ^ $2 ^ " := " ^ $4 ^ " " ^ $5 ^ "END TAGCASE"
  }
| TAGCASE value_name ASSIGN expression tag_list_colon_expression
  OTHERWISE COLON expression END TAGCASE
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[TAGCASE#4]:%s\n>"
      ("TAGCASE " ^ $2 ^ " := " ^ $4 ^ " " 
       ^ $5 ^ "OTHERWISE : " ^ $8 ^ "END TAGCASE");
    ("TAGCASE " ^ $2 ^ " := " ^ $4 ^ " " 
     ^ $5 ^ "OTHERWISE : " ^ $8 ^ "END TAGCASE");
  }
;

tag_list_colon_expression :
  tagnames COLON expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[tag_list_colon_expression]:%s\n>"
        ($1 ^ " : " ^ $3);
      ($1 ^ " : " ^ $3)
    }
;
tagnames : TAG names
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[TAG names]:%s\n>" $2;
      "TAG " ^ $2
    }
;


primary :
  constant
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[expression:%s#1]>\n" $1;
      $1
    }
|   OLD value_name
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[OLD :%s#1]>\n" ("OLD " ^ $2);
    ("OLD " ^ $2)
  }
|   value_name
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[value_name:%s#1]>\n" ($1);
    ($1)
  }
|   LPAREN expression RPAREN
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[LPAREN EXPN RPAREN:%s#1]>\n"
      ("(" ^ $2 ^ ")");
    ("(" ^ $2 ^ ")")
  }
|   invocation
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[function_invocation:%s#1]>\n" $1;
    $1
  }
;

iteration_exp:
  FOR
  INITIAL
  decldef_part
  iterator_terminator
  RETURNS return_exp_list
  END FOR
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:iterator FOR INITIAL>";
      "FOR " ^ " INITIAL " ^ $3 ^ " "
      ^ $4 ^ " RETURNS " ^ $6
      ^ " END FOR"
    }
| FOR
  INITIAL
  decldef_part
  SEMICOLON
  iterator_terminator
  RETURNS return_exp_list
  END FOR
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:iterator FOR INITIAL>";
      "FOR " ^ " INITIAL " ^ $3 ^ " "
      ^ $5 ^ " RETURNS " ^ $7
      ^ " END FOR"
    }
| FOR
  in_exp_list
  RETURNS
  return_exp_list
  END FOR
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:iterator FOR>";
    let k = str_forall_loop (`For (`Inexp_list $2, `Returns_list $4))
    in print_endline ("From types:" ^ k );
    "FOR " ^ " " ^ $2 ^ " RETURNS " ^ $4 ^ " END FOR"
  }

| FOR
  in_exp_list
  decldef_part
  RETURNS
  return_exp_list
  END FOR
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:iterator FOR>";
    "FOR " ^ " " ^ $2 ^ " " ^ $3 ^ " RETURNS " ^ $5 ^ " END FOR"
  }
|   FOR
  in_exp_list
  decldef_part
  SEMICOLON
  RETURNS
  return_exp_list
  END FOR
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:iterator FOR>";
    "FOR " ^ " " ^ $2 ^ " " ^ $3 ^ " RETURNS " ^ $6 ^ " END FOR"
  }

;

iterator_terminator:
  iterator termination_test
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:iterator termination_test>";
      $1 ^ " " ^ $2
    }
|   termination_test iterator
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:termination_test iterator>";
    $1 ^ " " ^ $2
  }
;

iterator:
  REPEAT iterator_body
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:REPEAT>";
      "REPEAT " ^ $2
    }
;

termination_test :
  WHILE expression
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:WHILE>";
      "WHILE"
    }
|   UNTIL expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:UNTIL>";
    "UNTIL"
  }
;

iterator_body :
  decldef_part
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:iterator_body>";
      $1
    }
| decldef_part SEMICOLON
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:iterator_body>";
      $1
    }

;

in_exp_list: in_exp_list DOT in_exp
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      let k = 
      $1 ^ " DOT " ^ $3
      in 
      parse_msg 5 "<Parsed:%s\n>" k ; k
    }
| in_exp_list CROSS in_exp
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      let k = 
      $1 ^ " CROSS " ^ $3
      in 
      parse_msg 5 "<Parsed:%s\n>" k ; k
    }
| in_exp
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      let k = $1 in
      parse_msg 5 "<Parsed:IN_EXP:%s\n>" k; k
    }
;

in_exp:
  NAME IN expression
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:IN_EXP>";
      $1 ^ " IN " ^ $3
    }
|   in_exp AT NAME
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:IN_EXP>";
    $1 ^ " AT " ^ $3
  }

;

return_exp_list:
  return_exp_list return_clause
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:return_clause_list>";
      $1 ^ $2
    }
|   return_clause
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:return_clause>";
    $1
  }
;
return_clause:
  OLD return_exp masking_clause
    {

      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:OLD return_exp>";
      "OLD " ^ $2 ^ " " ^ $3
    }
|   OLD return_exp
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:OLD return_exp>";
    "OLD " ^ $2
  }
|   return_exp masking_clause
  {
    let pst = String.make 7 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:return_exp with masking clause>";
    $1 ^ " " ^ $2
  }
|   return_exp
  {
    let pst = String.make 7 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:return_exp>";
    $1
  }
;
masking_clause:
  UNLESS expression
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:UNLESS>";
      "UNLESS " ^ $2
    }
|   WHEN expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:WHEN>";
    "WHEN " ^ $2
  }
;
return_exp:
  VALUE OF direction expression
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:VALUE OF>";
      "VALUE OF " ^ $3 ^ " " ^ $4
    }
|   VALUE OF direction reduction_op expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:VALUE OF>";
    "VALUE OF " ^ $3 ^ " " ^ $4 ^ " " ^ $5
  }
|   VALUE OF reduction_op expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:VALUE OF reduction_op>";
    "VALUE OF " ^ $3 ^ " " ^ $4
  }
|   VALUE OF expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:VALUE OF>";
    "VALUE OF " ^ $3
  }
|   ARRAY OF expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:ARRAY OF>";
    "ARRAY OF " ^ $3
  }
|   STREAM OF expression
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:STREAM OF>";
    "STREAM OF " ^ $3
  }
;
direction:
  LEFT
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:LEFT>";
      "LEFT"
    }
|   RIGHT
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:RIGHT>";
    "RIGHT"
  }
|   TREE
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:TREE>";
    "TREE"
  }
;
reduction_op:
  SUM 
    {
      let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:SUM>";
      "SUM"
    }
|   PRODUCT
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:PRODUCT>";
    "PRODUCT"
  }
|   LEAST
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:LEAST>";
    "LEAST"
  }
|   GREATEST
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:GREATEST>";
    "GREATEST"
  }
|   CATENATE
  {
    let pst = String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:CATENATE>";
    "CATENATE"
  }
;

let_in_exp :
  LET decldef_part IN expression END LET
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[decl_part#1]%s\n>"
        ("LET " ^ $2 ^ " IN " ^ $4 ^ " END LET");
      ("LET " ^ $2 ^ " IN " ^ $4 ^ " END LET")
    }
;

decldef_part :
  decldef
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[decl_part#1]%s\n>" $1;
      $1
    }
|   decldef_part SEMICOLON decldef
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[decl SEMICOLON#1]%s\n>" $1;
    $1
  }
;

decldef :
  decl
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[decl#1]%s\n>" $1;
      $1
    }
|   def
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[def#1]%s\n>" $1;
    $1
  }
|   decl_list ASSIGN expression
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[decl_list#1]%s\n>"
      ($1 ^ " ASSIGN " ^ $3);
    ($1 ^ "," ^ $3)
  }
;

decl_list :
  decl
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[decl_list#1]%s\n>" $1;
      $1
    }
|   decl_list COMMA decl
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[decl_list#1]%s\n>" ($1 ^ "," ^ $3);
    ($1 ^ "," ^ $3)
  }
;

decl : 
  field_spec
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_spec#1]%s\n>" $1;
      $1
    }
;

def :
  names ASSIGN expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[def#1]%s\n>" ($1 ^ " ASSIGN " ^ $3);
      $1 ^ " ASSIGN " ^ $3
    }
;

conditional_exp:
  conditional_ifexp conditional_else END IF
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    let k = 
    ($1 ^" " ^ $2 ^" END IF") in
    parse_msg 5 "<Parsed IF:%s>\n" k; k
  }
|   conditional_ifexp conditional_elseif conditional_else END IF
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    let k = 
    ($1 ^" " ^ $2 ^" " ^ $3 ^" END IF") in
    parse_msg 5 "<Parsed IF:%s>\n" k; k
  }
;

conditional_elseif:
  ELSEIF expression THEN expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:IF THEN ELSEIF exp>";
      " ELSEIF " ^ $2 ^ " THEN " ^ $4
    }
|   conditional_elseif ELSEIF expression THEN expression
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:IF THEN ELSEIF exp>";
    $1 ^ " ELSEIF " ^ $3 ^ " THEN " ^ $5 
  }
;

conditional_else:
ELSE expression
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:ELSE exp>";
    " ELSE " ^ $2
  }
;

conditional_ifexp:
  IF expression THEN expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:IF exp>";
      "{IF " ^ $2 ^ " THEN " ^ $4
    }       
;

union_test :
  IS tag_name LPAREN expression RPAREN
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[union_test:%s#1]>\n"
        ("IS " ^ $2 ^ "(" ^ $4 ^ ")");
      ("IS " ^ $2 ^ "(" ^ $4 ^ ")")
    }
;
union_generator :
  UNION type_name LBRACK tag_name RBRACK
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[union_generator:%s#1]>\n"
        ("UNION " ^ $2 ^ "[" ^ $4 ^ "]");
      "UNION " ^ $2 ^ "[" ^ $4 ^ "]"
    }
| UNION type_name LBRACK tag_name COLON expression RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[union_generator:%s#1]>\n"
      ("UNION " ^ $2 ^ "[" ^ $4 ^ ":" ^ $6 ^ "]");
    "UNION " ^ $2 ^ "[" ^ $4 ^ ":" ^ $6 ^ "]"
  }
;
error_test :
  IS ERROR LPAREN expression RPAREN
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[error_test#1]%s\n>" ("IS ERROR (" ^ $4 ^")");
      "IS ERROR (" ^ $4 ^")"
    }
;
//%inline
  tag_name : NAME
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_name#1]%s\n>" $1;
      $1
    }
;

prefix_operation :
  prefix_name LPAREN expression RPAREN
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[prefix_operation:%s#1]>\n"
        ($1 ^ "(" ^ $3 ^ ")");
      $1 ^ "(" ^ $3 ^ ")"
    }
;
//%inline
  prefix_name :
  CHARACTER
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:[CHARACTER#1]>";
      "CHARACTER"
    }
| DOUBLE_REAL
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[DOUBLE_REAL#1]>";
    "DOUBLE_REAL"
  }
| INTEGER
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[INTEGER#1]>";
    "INTEGER"
  }
| REAL
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[REAL#1]>";
    "REAL"
  }

;

constant : FALSE
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[constant#2]:%s>\n" ("FALSE");
      "FALSE"
    }
| NIL
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[constant#1]:%s>\n" ("NIL");
    "NIL"
  }
| TRUE
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[constant#2]:%s>\n" ("TRUE");
    "TRUE"
  }
| INT
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[integer]:%d>\n" ($1);
    string_of_int $1
  }
| FLOAT
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[float]:%f>\n" ($1);
    string_of_float $1
  }
| CHAR
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[character#2]:%s>\n" ($1);
    $1
  }
| STRING
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[string#2]:%s>\n" ($1);
    $1
  }
| ERROR LBRACK type_spec RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[erro lbrack type_spec#2]:%s>\n"
      ("ERROR [" ^ $3 ^ "]");
    "ERROR [" ^ $3 ^ "]"
  }
;

type_def_part: type_def
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[type_def#2]:%s>\n" $1;
      $1
    }
|   type_def_part SEMICOLON type_def
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[type_def_part#2]:%s>\n" ($1 ^ ";" ^ $3);
    ($1 ^ ";" ^ $3)
  }
;
type_def : TYPE type_name EQ type_spec
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[type_def#1]:%s>\n" ("TYPE:" ^ $2 ^ " = " ^ $4);
      "TYPE " ^ $2 ^ " = " ^ $4
    }
;
type_spec : basic_type_spec
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:[basic_type_spec#2]>";
      $1
    }
|   compound_type_spec
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[compound_type_spec#2]>";
    $1
  }
|   type_name
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[type_name#2]>";
    $1
  } 
;
type_name : NAME
    {
      $1
    }
;

basic_type_spec :
  BOOLEAN
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:[BOOLEAN#1]>";
      let k = str_sisal_type `Boolean
      in print_endline ("From type:"  ^k );
      "BOOLEAN"
    }
| prefix_name
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[prefix_name#1]>";
    $1
  }
| NULL
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[NULL#1]>";
    let k = str_sisal_type `Null
    in print_endline ("From type: " ^ k);
    "NULL"
  }
;

compound_type_spec :
  ARRAY LBRACK type_spec RBRACK
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:[ARRAY#1]>";
      "ARRAY [" ^ $3 ^ "]"
    }
|   STREAM LBRACK type_spec RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[STREAM#1]>";
    "STREAM [" ^ $3 ^ "]"
  }
|   RECORD LBRACK field_spec_list RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" ("<Parsed:<"^"RECORD [" ^ $3 ^ "]>");
    "RECORD [" ^ $3 ^ "]"
  }
|   UNION LBRACK tag_spec_list RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[UNION#1]:%s\n>" ("UNION [" ^ $3 ^ "]");
    "UNION [" ^ $3 ^ "]"
  }

;

tag_spec_list: field_spec_list
    {
      $1
    }
| names_list
  {
    $1
  }
;

field_spec_list:
  field_spec 
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:[FIELD_SPEC#1]>";
      $1
    }
| field_spec_list SEMICOLON field_spec
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[field_spec_list#1]>";
    $1 ^ ";" ^ $3
  }
;


field_spec : names COLON type_spec
    {
      $1 ^ ":" ^ $3
    }
;

names_list : 
  names 
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "%s\n" "<Parsed:[bunchofnames#1]>";
      $1
    }
|  names_list SEMICOLON names
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "%s\n" "<Parsed:[bunchofnames with SEMI#1]>";
    $1 ^ ";" ^ $3
  }
;

names : names COMMA NAME
    {
      $1 ^ "," ^ $3
    }
|   NAME
  {
    $1
  }
;
value_name : NAME
    {
      $1
    }
;

invocation : 
  function_name LPAREN RPAREN
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[invocation:%s#1]>\n"
        ($1 ^ "()");
      ($1 ^ "()")
    }
|   function_name LPAREN expression RPAREN
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[invocation:%s#2]>\n"
      ($1 ^ "(" ^ $3 ^ ")");
    ($1 ^ "(" ^ $3 ^ ")")
  }
;
function_name : NAME
    {
      $1
    }
;
array_ref :
  primary LBRACK expression RBRACK
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[array_ref:%s#1]>\n"
        ($1 ^ "[" ^ $3 ^ "]");
      ($1 ^ "[" ^ $3 ^ "]")
    }
;

array_generator :
  ARRAY type_name LBRACK RBRACK
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[array_generator:%s#1]>\n"
        ("ARRAY " ^ $2 ^ "[]");
      "ARRAY " ^ $2 ^ "[]"
    }
|    ARRAY LBRACK expr_pair RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[array_generator:%s#2]>\n"
      ("ARRAY [" ^ $3 ^ "]");
    "ARRAY " ^ "[" ^ $3 ^ "]"
  }

|    ARRAY type_name LBRACK expr_pair RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[array_generator:%s#2]>\n"
      ("ARRAY " ^ $2 ^ "[]");
    "ARRAY " ^ $2 ^ "[" ^ $4 ^ "]"
  }
|    primary LBRACK expr_pair_list RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[array_generator:%s#3]>\n"
      ($1 ^ "[" ^ $3 ^ "]") ;
    $1 ^ "[" ^ $3 ^ "]"
  }
|    primary LBRACK expr_pair_list SEMICOLON RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[array_generator:%s#3]>\n"
      ($1 ^ "[" ^ $3 ^ "]") ;
    $1 ^ "[" ^ $3 ^ "]"
  }
;

expr_pair_list :
  expr_pair
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[EXPR_PAIR:%s#1]>\n" $1;
      $1
    }
|   expr_pair_list SEMICOLON expr_pair
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[EXPR_PAIR:%s#1]>\n" 
      ($1 ^ ";" ^ $3);
    $1 ^ ";" ^ $3
  }
;
expr_pair :
  expression COLON expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[EXPR_PAIR:%s#1]>\n" ($1 ^ ":" ^ $3);
      $1 ^ ":" ^ $3
    }
;
stream_generator :
  STREAM type_name LBRACK RBRACK
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[STREAM:%s#1]>\n" ("STREAM " ^ $2 ^ "[]");
      ("STREAM " ^ $2 ^ "[]")
    }
;
| STREAM type_name LBRACK expression RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[STREAM:%s#1]>\n"
      ("STREAM " ^ $2 ^ "[" ^ $4 ^ "]");
    ("STREAM " ^ $2 ^ "[" ^ $4 ^ "]")
  }
;

record_ref :
  primary DOTSTOP field_name
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[record_ref:%s#1]>\n" ($1 ^ "." ^ $3);
      $1 ^ "." ^ $3
    }
;

record_generator :
  RECORD type_name LBRACK field_def_list RBRACK
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[record_generator:%s#1]>\n"
        ("RECORD " ^ $2 ^ "[" ^ $4 ^ "]");
      "RECORD " ^ $2 ^ "[" ^ $4 ^ "]"
    }
|  RECORD type_name LBRACK field_def_list SEMICOLON RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[record_generator:%s#2]>\n"
      ("RECORD " ^ $2 ^ "[" ^ $4 ^ "]");
    "RECORD " ^ $2 ^ "[" ^ $4 ^ "]"
  }
|   RECORD LBRACK field_def_list RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[record_generator:%s#3]>\n"
      ("RECORD " ^ "[" ^ $3 ^ "]");
    "RECORD " ^ "[" ^ $3 ^ "]"
  }
|  RECORD LBRACK field_def_list SEMICOLON RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[record_generator:%s#4]>\n"
      ("RECORD " ^ "[" ^ $3 ^ "]");
    "RECORD " ^ "[" ^ $3 ^ "]"
  }
|  primary REPLACE LBRACK field_list RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[record_generator:%s#1]>\n"
      ($1 ^ " REPLACE [" ^ $4 ^ "]");
    ($1 ^ " REPLACE [" ^ $4 ^ "]")

  }
|  primary REPLACE LBRACK field_list SEMICOLON RBRACK
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[record_generator:%s#1]>\n"
      ($1 ^ " REPLACE [" ^ $4 ^ "]");
    ($1 ^ " REPLACE [" ^ $4 ^ "]")
  }
;

field_def_list :
  field_def
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_def:%s#1]>\n" $1;
      $1
    }
| field_def_list SEMICOLON field_def
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[field_def:%s#1]>\n" ($1 ^ ";" ^ $3);
    $1 ^ ";" ^ $3
  }
;
field_def : field_name COLON expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_def:%s#1]>\n" ($1 ^ ":" ^ $3);
      ($1 ^ ":" ^ $3)
    }
;
field_list :
  field_expn
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_list:%s#1]>\n" $1;
      $1
    }
|   field_list SEMICOLON field_expn
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[field_list:%s#1]>\n" $1;
    $1 ^ ";" ^ $3
  }
;
field_expn :
  field COLON expression
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_list:%s#1]>\n" $1;
      $1 ^ ":" ^ $3
    }
;
field : field_name
    {
      let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
      parse_msg 5 "<Parsed:[field_name:%s#1]>\n" $1;
      $1
    }
| field DOTSTOP field_name
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[field:%s#r]>\n" ($1 ^ "." ^ $3);
    $1 ^ "." ^ $3
  }
;

field_name : NAME
  {
    let pst =  String.make 5 ' ' in parse_msg 5 "%s" pst;
    parse_msg 5 "<Parsed:[field_name#1]%s\n>" $1;
    $1
  }
;

main: compilation_unit
  {
    $1
  }
;

