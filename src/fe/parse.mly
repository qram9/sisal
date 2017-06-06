%{

exception ParseErr of string

open Type
open Lexing
open Parsing
  let debug_level = ref 3
let error msg start finish = 
  Printf.sprintf "(line %d: char %d..%d): %s" start.pos_lnum 
    (start.pos_cnum -start.pos_bol) (finish.pos_cnum - finish.pos_bol) msg

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
%type <Type.compilation_unit> main
%start main
%%
compilation_unit :
  def_func_name_list
    function_def_list EOF
    {
      let t:Type.compilation_unit =
        Compilation_unit ($1,[],[],$2)
      in t
    }
| def_func_name_list
    type_def_part
    function_def_list EOF
  {
    let t:Type.compilation_unit =
      Compilation_unit ($1,$2,[],$3)
    in t
  }
| def_func_name_list
    type_def_part
    global_header_list
    function_def_list EOF
  {
    let t:Type.compilation_unit =
      Compilation_unit ($1,$2,$3,$4)
    in t
  }
| def_func_name_list
    type_def_part
    SEMICOLON
    function_def_list EOF
  {
    let t:Type.compilation_unit =
      Compilation_unit ($1,$2,[],$4)
    in t
  }
| def_func_name_list
    type_def_part
    SEMICOLON
    global_header_list
    function_def_list EOF
  {
    let t:Type.compilation_unit =
      Compilation_unit ($1,$2,$4,$5)
    in t
  }
;

global_header_list :
  GLOBAL function_header
    {
      [$2]
    }
| global_header_list GLOBAL function_header
  {
    $1@[$3]
  }
;

def_func_name_list:
  DEFINE function_name_list
    {
      let t:Type.define =
        Define $2
      in t
    }
;

function_name_list :
  function_name_list NAME
    {
      $1@[(Function_name $2)]
    }
| NAME
  {
    let t:Type.function_name =
      Function_name $1
    in [t]
  }
;

function_def_list: function_def
    {
      [$1]
    }
| function_def_list function_def
  {
    $1@[$2]
  }
;

function_def:
  FORWARD FUNCTION function_header
    {
      let t:Type.function_def =
        Forward_function $3
      in t
    }
| function_nest
  {
    let t:Type.function_def =
      Function $1
    in t
  }
;

function_nest:
FUNCTION function_header function_nest expression END FUNCTION
  {
    let t =
    ($2,[],$3,$4)
    in [Function_single t]
  }
|   FUNCTION function_header type_def_part SEMICOLON function_nest expression END FUNCTION
  {
    let t =
    ($2,$3,$5,$6)
    in [Function_single t]
  }
|   FUNCTION function_header type_def_part function_nest expression END FUNCTION
  {
    let t =
    ($2,$3,$4,$5)
    in [Function_single t]
  }

| FUNCTION function_header expression END FUNCTION
  {
    let t =
    ($2,[],[],$3)
    in [Function_single t]
  }
|   FUNCTION function_header type_def_part SEMICOLON expression END FUNCTION
  {
    let t =
    ($2,$3,[],$5)
    in [Function_single t]
  }
|   FUNCTION function_header type_def_part expression END FUNCTION
  {
    let t =
    ($2,$3,[],$4)
    in [Function_single t]
  }
;

function_header : 
  function_name LPAREN RETURNS type_list RPAREN
    {
      let t:Type.function_header =
        Function_header_nodec ($1,$4) in t
    }
| function_name LPAREN decl_list_semi RETURNS type_list RPAREN
  {
    let t:Type.function_header =
      Function_header ($1,$3,$5) in t
  }
;

decl_list_semi:
  decl
  { 
    [$1] 
  }
| decl_list_semi SEMICOLON decl
  {
    $1@[$3]
  }
;

type_list :
  type_spec
    {
      [$1]
    }
|   type_list COMMA type_spec
  {
      $1@[$3]
  }
;
expression: exp_list
    {
      Exp $1
    }
;
exp_list :
  simple_expression
  {
    [$1]
  }
|  exp_list COMMA simple_expression
  {
    $1@[$3]
  }
;

simple_expression:
  primary_part2
    {
      $1
    }
| simple_expression   GT simple_expression 
  {
    let t:Type.simple_exp =
      Greater ($1,$3)
    in t
  }
| simple_expression   GE simple_expression 
  {
    let t:Type.simple_exp =
      Greater_equal($1,$3) 
    in t
  }
| simple_expression
  LT
  simple_expression 
  {
    let t:Type.simple_exp =
      Lesser ($1,$3)
    in t
  }

| simple_expression
  LE
  simple_expression 
  {
    let t:Type.simple_exp =
      Lesser_equal ($1,$3)
    in t
  }

| simple_expression
  EQ
  simple_expression 
  {
    let t:Type.simple_exp =
      Equal($1,$3) 
    in t
  }

| simple_expression
  NE
  simple_expression 
  { 
    let t:Type.simple_exp =
      Not_equal ($1,$3) 
    in t
  }

| simple_expression
  PLUS
  simple_expression 
  {
    let t:Type.simple_exp =
      Add ($1,$3) 
    in t
  }

| simple_expression
  MINUS
  simple_expression
  { 
    let t:Type.simple_exp =
      Subtract ($1,$3) 
    in t
  }

| simple_expression
  OR
  simple_expression 
  {
    let t:Type.simple_exp =
      Or ($1,$3) 
    in t
  }

| simple_expression
  STAR
  simple_expression 
  {
    let t:Type.simple_exp =
      Multiply ($1,$3) 
    in t
  }
| simple_expression
  DIVIDE
  simple_expression 
  {
    let t:Type.simple_exp =
      Divide ($1,$3) 
    in t
  }
| simple_expression
  AND
  simple_expression 
  {
    let t:Type.simple_exp =
      And ($1,$3)
    in t
  }
| simple_expression
  PIPE
  simple_expression 
  {
    let t:Type.simple_exp =
      Pipe ($1, $3)
    in t
  }
|  PLUS simple_expression
  {
    let t:Type.simple_exp =
      $2
    in t
  }
|   MINUS simple_expression %prec UMINUS
  {
    let t:Type.simple_exp =
      Negate $2
    in t
  }
|   NOT simple_expression %prec UMINUS
  {
    let t:Type.simple_exp =
    Not $2
    in t 
  }

;

primary_part2 :
  primary
    {
      $1
    }
|  array_ref
  {
    $1
  }
|   array_generator
  {
    $1
  }
|   stream_generator
  {
    $1
  }
|   record_ref
  {
    $1
  }
|   record_generator
  {
    $1
  }
|   union_test
  {
    $1
  }
|   union_generator
  {
    $1
  }
|   error_test
  {
    $1
  }
|   prefix_operation
  {
    $1
  }
|   conditional_exp
  {
    $1
  }
|   let_in_exp
  {
    $1
  }
|   tagcase_exp
  {
    $1
  }
|   iteration_exp
  {
    $1
  }
;

array_ref :
  primary LBRACK expression RBRACK
    {
      let t:Type.simple_exp = Array_ref ($1,$3) in t
    }
;

array_generator :
  ARRAY type_name LBRACK RBRACK
    {
      let t:(Type.simple_exp) = Array_generator_named $2 in t
    }
|    ARRAY LBRACK expr_pair RBRACK
  {
    let t:(Type.simple_exp) = Array_generator_unnamed $3 in t
  }
|    ARRAY type_name LBRACK expr_pair RBRACK
  {
    let t:(Type.simple_exp) = Array_generator_named_addr ($2,$4) in t
  }
|    primary LBRACK expr_pair_list RBRACK
  {
    let t:(Type.simple_exp) = Array_generator_primary ($1,$3) in t
  }
|    primary LBRACK expr_pair_list SEMICOLON RBRACK
  {
    let t:(Type.simple_exp) = Array_generator_primary ($1,$3) in t
  }
;

expr_pair_list :
  expr_pair
    {
      [$1]
    }
|   expr_pair_list SEMICOLON expr_pair
  {
    $1@[$3]
  }
;
expr_pair :
  expression COLON expression
    {
      let t:(Type.expr_pair) = Expr_pair ($1,$3) in t
    }
;
stream_generator :
  STREAM type_name LBRACK RBRACK
    {
      let t:(Type.simple_exp) = Stream_generator ($2) in t
    }
| STREAM type_name LBRACK expression RBRACK
  {
    let t:(Type.simple_exp) = Stream_generator_exp ($2,$4) in t
  }
;

record_ref :
  primary DOTSTOP field_name
    {
      let t:(Type.simple_exp) = Record_ref ($1,$3) in t
    }
;

record_generator :
  RECORD type_name LBRACK field_def_list RBRACK
    {
      let t:Type.simple_exp =
        Record_generator_named ($2,$4) in t
    }
|  RECORD type_name LBRACK field_def_list SEMICOLON RBRACK
  {
    let t:Type.simple_exp =
      Record_generator_named ($2,$4) in t
  }
|   RECORD LBRACK field_def_list RBRACK
  {
    let t:Type.simple_exp =
      Record_generator_unnamed $3 in t
  }
|  RECORD LBRACK field_def_list SEMICOLON RBRACK
  {
    let t:Type.simple_exp =
      Record_generator_unnamed $3 in t
  }
|  primary REPLACE LBRACK field_list RBRACK
  {
    let t:Type.simple_exp =
      Record_generator_primary ($1, $4) in t
  }
|  primary REPLACE LBRACK field_list SEMICOLON RBRACK
  {
    let t:Type.simple_exp =
      Record_generator_primary ($1, $4) in t
  }
;

field_def_list :
  field_def
    {
      [$1]
    }
| field_def_list SEMICOLON field_def
  {
    $1@[$3]
  }
;

field_def : field_name COLON expression
    {
      let k:Type.field_def = Field_def ($1,$3) in k
    }
;
field_list :
  field_expn
    {
      [$1]
    }
|   field_list SEMICOLON field_expn
  {
    $1@[$3]
  }
;
field_expn :
  field COLON expression
    {
      let k:Type.field_exp = Field_exp (Field $1,$3) in k
    }
;

tagcase_exp :
  TAGCASE expression tag_list_colon_expression_list END TAGCASE
    {
      let t:(Type.simple_exp) =
        Tagcase (Tagcase_exp $2, $3, Otherwise Empty) in t
    }
| TAGCASE expression tag_list_colon_expression_list OTHERWISE COLON expression END TAGCASE
  {
    let t:(Type.simple_exp) =
      Tagcase (Tagcase_exp $2, $3, Otherwise $6) in t
  }
| TAGCASE value_name ASSIGN expression tag_list_colon_expression_list END TAGCASE
  {
    let t:(Type.simple_exp) =
      Tagcase (Assign (Value_name $2,$4), $5,Otherwise Empty) in t
  }
| TAGCASE value_name ASSIGN expression tag_list_colon_expression_list
  OTHERWISE COLON expression END TAGCASE
  {
    let t:(Type.simple_exp) =
      Tagcase (Assign (Value_name $2,$4), $5, Otherwise $8) in t
  }
;

tag_list_colon_expression_list :
tag_list_colon_expression
  {
        [$1]
  }
|tag_list_colon_expression_list  tag_list_colon_expression
  {
    $1@[$2]
  }
;

tag_list_colon_expression :
  tagnames COLON expression
    {
      let t:(Type.tagnames_colon_exp) =
        Tag_list ($1,$3) in t
    }
;

tagnames : TAG names
    {
      let t:Type.tagnames =
      Tagnames $2 in t
    }
;

primary :
  constant
    {
      let t:Type.simple_exp = Constant $1
      in t
    }
|   OLD value_name
  {
    let t:Type.simple_exp = Old (Value_name $2) in t
  }
|   value_name
  {
    let t:Type.simple_exp = Val (Value_name $1) in t
  }
|   LPAREN expression RPAREN
  {
    let t:Type.simple_exp = Paren $2 in t
  }
|   invocation
  {
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
      let t:Type.simple_exp =
        For_initial (Decldef_part $3,$4,$6) in t
    }
| FOR
  INITIAL
  decldef_part
  SEMICOLON
  iterator_terminator
  RETURNS return_exp_list
  END FOR
    {
      let t:Type.simple_exp =
        For_initial (Decldef_part $3,$5,$7) in t
    }
| FOR
  in_exp_list
  RETURNS
  return_exp_list
  END FOR
  {
    let t:Type.simple_exp =
      For_all ($2,Decldef_part [],$4) in t
  }

| FOR
  in_exp_list
  decldef_part
  RETURNS
  return_exp_list
  END FOR
  {
    let t:Type.simple_exp =
      For_all ($2,Decldef_part $3,$5) in t
  }
|   FOR
  in_exp_list
  decldef_part
  SEMICOLON
  RETURNS
  return_exp_list
  END FOR
  {
    let t:Type.simple_exp =
      For_all ($2,Decldef_part $3,$6) in t
  }
;

iterator_terminator:
  iterator termination_test
    {
      let t:(iterator_terminator) =
        Iterator_termination ($1,$2) in t
    }
|   termination_test iterator
  {
    let t:(iterator_terminator) =
      Termination_iterator ($1,$2) in t
  }
;

iterator:
  REPEAT iterator_body
    {
      let t:(Type.iterator) =
      Repeat $2 in t
    }
;

termination_test :
  WHILE expression
    {
      let t:(Type.termination_test) =
      While $2 in t
    }
|   UNTIL expression
  {
    let t:(Type.termination_test) =
    Until $2 in t
  }
;

iterator_body :
  decldef_part
    {
      Decldef_part $1
    }
| decldef_part SEMICOLON
    {
      Decldef_part $1
    }

;

in_exp_list: in_exp_list DOT in_exp
    {
      let t:(Type.in_exp) =
      Dot($1,$3) in t
    }
| in_exp_list CROSS in_exp
    {
      let t:(Type.in_exp) =
      Cross ($1,$3) in t
    }
| in_exp
    {
       $1
    }
;

in_exp:
  NAME IN expression
    {
      let t:(Type.in_exp) =
        In_exp (Value_name $1, $3) in t
    }
|   in_exp AT NAME
  {
    let t:(Type.in_exp) =
      At_exp ($1, Value_name $3) in t
  }
;

return_exp_list:
  return_exp_list return_clause
    {
      $1@[$2]
    }
|   return_clause_old
  {
    [$1]
  }
|   return_clause
  {
    [$1]
  }
;
return_clause_old:
  OLD return_exp masking_clause
    {
      let t:(return_clause)  =
        Old_ret  ($2, $3) in t
    }
|   OLD return_exp
  {
    let t:(return_clause)  =
      Old_ret ($2, No_mask) in t
  }
;
return_clause:
return_exp masking_clause
  {
    let t:(return_clause)  =
    Return_exp ($1, $2) in t
  }
|   return_exp
  {
    let t:(return_clause)  =
    Return_exp ($1, No_mask) in t
  }
;
masking_clause:
  UNLESS expression
    {
      Unless $2
    }
|   WHEN expression
  {
    let t:(Type.masking_clause) = When $2 in t
  }
;

return_exp:
  VALUE OF direction expression
    {
      let t:(Type.return_exp) = Value_of ($3, No_red, $4)
      in t 
    }
|   VALUE OF direction reduction_op expression
  {
    let t:(Type.return_exp) = Value_of ( $3, $4, $5)
    in t
  }
|   VALUE OF reduction_op expression
  {
    let t:(Type.return_exp) = Value_of (No_dir, $3, $4)
    in t
  }
|   VALUE OF expression
  {
    let t:(Type.return_exp) =
      Value_of (No_dir,No_red,$3) in t
  }
|   ARRAY OF expression
  {
    let t:(Type.return_exp) = Array_of $3 in t
  }
|   STREAM OF expression
  {
    let t:(Type.return_exp) = Stream_of $3 in t
  }
;

direction:
  LEFT
    {
      Left
    }
|   RIGHT
  {
    Right
  }
|   TREE
  {
    let t:Type.direction_op = Tree in t
  }
;
reduction_op:
  SUM 
    {
      Sum
    }
|   PRODUCT
  {
    Product
  }
|   LEAST
  {
    Least
  }
|   GREATEST
  {
    Greatest
  }
|   CATENATE
  {
    let t:Type.reduction_op = Catenate in t
  }
;

let_in_exp :
  LET decldef_part IN expression END LET
    {
      let t:Type.simple_exp = Let (Decldef_part $2,$4) in t
    }
;

decldef_part :
  decldef
    {
      [$1]
    }
|   decldef_part SEMICOLON decldef
  {
    $1@[$3]
  }
;

decldef :
  decl
    {
      Decl_decl $1
    }
|   def
  {
    Decl_def $1
  }
|   decl_list ASSIGN expression
  {
    let t:(Type.decldef) = Decldef ($1,$3) in t
  }
;

decl_list :
  decl
    {
      [$1]
    }
|   decl_list COMMA decl
  {
    $1@[$3]
  }
;

decl : 
  names COLON type_spec
    {
      Decl ($1,$3)
    }
;

def :
  names ASSIGN expression
    {
      Def ($1,$3)
    }
;

conditional_exp:
  conditional_ifexp conditional_else END IF
  {
    let t:(Type.simple_exp) = If ([$1],$2) in t
  }
|   conditional_ifexp conditional_elseif conditional_else END IF
  {
    let t:(Type.simple_exp) = If ($1::$2,$3) in t
  }
;

conditional_elseif:
  ELSEIF expression THEN expression
    {
      let t:(Type.cond) = 
        Cond ($2,$4) in [t]
    }
|   conditional_elseif ELSEIF expression THEN expression
  {
    $1@[let t:(Type.cond) = Cond ($3,$5) in t]
  }
;

conditional_else:
ELSE expression
  {
    let t:(Type.last_else) = Else $2 in t
  }
;

conditional_ifexp:
  IF expression THEN expression
    {
      let t:(cond) = Cond ($2,$4) in t
    }       
;

union_test :
  IS tag_name LPAREN expression RPAREN
    {
      let t:(Type.simple_exp) = Is ($2,$4) in t
    }
;
union_generator :
  UNION type_name LBRACK tag_name RBRACK
    {
      let t:Type.simple_exp = Union_generator ($2,Tag_name $4) in t
    }
| UNION type_name LBRACK tag_name COLON expression RBRACK
  {
    let t:Type.simple_exp = Union_generator ($2,Tag_exp ($4,$6)) in t
  }
;
error_test :
  IS ERROR LPAREN expression RPAREN
    {
      let t:Type.simple_exp = Is_error $4 in t
    }
;
  tag_name : NAME
    {
      let t:Type.tag_name = $1 in t
    }
;

prefix_operation :
  prefix_name LPAREN expression RPAREN
    {
      let k:Type.simple_exp = 
       Prefix_operation ($1,$3) in k
    }
;
  prefix_name :
  CHARACTER
    {
      let k:Type.prefix_name = Char_prefix in k
    }
| DOUBLE_REAL
  {
      let k:Type.prefix_name = Double_prefix in k
  }
| INTEGER
  {
      let k:Type.prefix_name = Integer_prefix in k
  }
| REAL
  {
      let k:Type.prefix_name = Real_prefix in k
  }
;

constant : FALSE
    {
      let k:Type.sisal_constant = False in k
    }
| NIL
  {
    let k:Type.sisal_constant = Nil in k
  }
| TRUE
  {
    let k:Type.sisal_constant = True in k
  }
| INT
  {
    let k:Type.sisal_constant = Int $1 in k
  }
| FLOAT
  {
    let k:Type.sisal_constant = Float $1 in k
  }
| CHAR
  {
    let k:Type.sisal_constant = Char $1 in k
  }
| STRING
  {
    let k:Type.sisal_constant = String $1 in k
  }
| ERROR LBRACK type_spec RBRACK
  {
    let k:Type.sisal_constant = Error $3 in k
  }
;

type_def_part: type_def
    {
      [$1]
    }
|   type_def_part SEMICOLON type_def
  {
    $1@[$3]
  }
;
type_def : TYPE type_name EQ type_spec
    {
      let k:Type.type_def = Type_def ($2, $4)
      in k
    }
;
type_spec : basic_type_spec
    {
      $1
    }
|   compound_type_spec
  {
    Compound_type $1
  }
|   type_name
  {
    Type_name $1
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
      let k:Type.sisal_type = Boolean in k
    }
| CHARACTER
    {
      let k:Type.sisal_type = Character in k
    }
| DOUBLE_REAL
  {
      let k:Type.sisal_type = Double_real in k
  }
| INTEGER
  {
      let k:Type.sisal_type = Integer in k
  }
| NULL
  {
    let k:Type.sisal_type = Null in k
  }
| REAL
  {
      let k:Type.sisal_type = Real in k
  }
;

compound_type_spec :
  ARRAY LBRACK type_spec RBRACK
    {
      let k:Type.compound_type = Sisal_array $3 in k
    }
|   STREAM LBRACK type_spec RBRACK
  {
      let k:Type.compound_type = Sisal_stream $3 in k
  }
|   RECORD LBRACK field_spec_list RBRACK
  {
      let k:Type.compound_type = Sisal_record $3 in k
  }
|   UNION LBRACK tag_spec_list RBRACK
  {
      let k:Type.compound_type = Sisal_union $3 in k
  }
|   UNION LBRACK names RBRACK
  {
      let k:Type.compound_type = Sisal_union_enum $3 in k
  }
;

field_spec_list:
  field_spec 
    {
      [$1]
    }
| field_spec_list SEMICOLON field_spec
  {
    $1@[$3]
  }
;

field_spec :
  names COLON type_spec
    {
      let k:Type.field_spec =
      Field_spec ($1,$3) in k
    }
;

names : names COMMA NAME
    {
      $1@[$3]
    }
|   NAME
  {
    [$1]
  }
;

tag_spec_list : 
  names COLON type_spec
    {
      ($1,$3)
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
      let t:(Type.simple_exp) =
        Invocation ($1,Arg Empty) in t
    }
|   function_name LPAREN expression RPAREN
  {
    let t:(Type.simple_exp) =
      Invocation ($1,Arg $3) in t
  }
;
function_name : NAME
    {
      let t:(Type.function_name) =
      Function_name $1 in t
    }
;
field : field_name
    {
      [$1]
    }
| field DOTSTOP field_name
  {
    $1@[$3]
  }
;

field_name : NAME
  {
    let k:Type.field_name = Field_name $1
    in k
  }
;

main: compilation_unit
  {
    $1
  }
;

