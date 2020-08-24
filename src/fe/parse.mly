%{

exception ParseErr of string

open Ast
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
%token ANDKW
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
%token REC
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
%type <Ast.compilation_unit> main
%start main
%%
compilation_unit :
  def_func_name_list
    function_def_list EOF
    {
      let t:Ast.compilation_unit =
        Compilation_unit ($1,[],[],$2)
      in t
    }
| def_func_name_list
    type_def_part
    function_def_list EOF
  {
    let t:Ast.compilation_unit =
      Compilation_unit ($1,$2,[],$3)
    in t
  }
| def_func_name_list
    type_def_part
    global_header_list
    function_def_list EOF
  {
    let t:Ast.compilation_unit =
      Compilation_unit ($1,$2,$3,$4)
    in t
  }
| def_func_name_list
    type_def_part
    SEMICOLON
    function_def_list EOF
  {
    let t:Ast.compilation_unit =
      Compilation_unit ($1,$2,[],$4)
    in t
  }
| def_func_name_list
    type_def_part
    SEMICOLON
    global_header_list
    function_def_list EOF
  {
    let t:Ast.compilation_unit =
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
      let t:Ast.define =
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
    let t:Ast.function_name =
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
      let t:Ast.function_def =
        Forward_function $3
      in t
    }
| function_nest
  {
    let t:Ast.function_def =
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
      let t:Ast.function_header =
        Function_header_nodec ($1,$4) in t
    }
| function_name LPAREN declids_spec_list RETURNS type_list RPAREN
  {
    let t:Ast.function_header =
      let wrapped = List.map (fun (x,y) -> Decl_some (x,y) ) $3 in
      Function_header ($1,wrapped,$5) in t
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
    let t:Ast.simple_exp =
      Greater ($1,$3)
    in t
  }
| simple_expression   GE simple_expression
  {
    let t:Ast.simple_exp =
      Greater_equal($1,$3)
    in t
  }
| simple_expression
  LT
  simple_expression
  {
    let t:Ast.simple_exp =
      Lesser ($1,$3)
    in t
  }
| simple_expression
  LE
  simple_expression
  {
    let t:Ast.simple_exp =
      Lesser_equal ($1,$3)
    in t
  }

| simple_expression
  EQ
  simple_expression
  {
    let t:Ast.simple_exp =
      Equal($1,$3)
    in t
  }

| simple_expression
  NE
  simple_expression
  {
    let t:Ast.simple_exp =
      Not_equal ($1,$3)
    in t
  }

| simple_expression
  PLUS
  simple_expression
  {
    let t:Ast.simple_exp =
      Add ($1,$3)
    in t
  }

| simple_expression
  MINUS
  simple_expression
  {
    let t:Ast.simple_exp =
      Subtract ($1,$3)
    in t
  }

| simple_expression
  OR
  simple_expression
  {
    let t:Ast.simple_exp =
      Or ($1,$3)
    in t
  }

| simple_expression
  STAR
  simple_expression
  {
    let t:Ast.simple_exp =
      Multiply ($1,$3)
    in t
  }
| simple_expression
  DIVIDE
  simple_expression
  {
    let t:Ast.simple_exp =
      Divide ($1,$3)
    in t
  }
| simple_expression
  AND
  simple_expression
  {
    let t:Ast.simple_exp =
      And ($1,$3)
    in t
  }
| simple_expression
  PIPE
  simple_expression
  {
    let t:Ast.simple_exp =
      Pipe ($1, $3)
    in t
  }
|  PLUS simple_expression
  {
    let t:Ast.simple_exp =
      $2
    in t
  }
|   MINUS simple_expression %prec UMINUS
  {
    let t:Ast.simple_exp =
      Negate $2
    in t
  }
|   NOT simple_expression %prec UMINUS
  {
    let t:Ast.simple_exp =
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
      let t:Ast.simple_exp = Array_ref ($1,$3) in t
    }
;

array_generator :
  ARRAY type_name LBRACK RBRACK
    {
      let t:(Ast.simple_exp) = Array_generator_named $2 in t
    }
|    ARRAY LBRACK simple_expr_pair RBRACK
  {
    let t:(Ast.simple_exp) = Array_generator_unnamed $3 in t
  }
|    ARRAY type_name LBRACK simple_expr_pair RBRACK
  {
    let t:(Ast.simple_exp) = Array_generator_named_addr ($2,$4) in t
  }
|    primary LBRACK simple_expr_pair_list RBRACK
  {
    let t:(Ast.simple_exp) = Array_replace ($1,$3) in t
  }
|    primary LBRACK simple_expr_pair_list SEMICOLON RBRACK
  {
    let t:(Ast.simple_exp) = Array_replace ($1,$3) in t
  }
;

simple_expr_pair_list :
simple_expr_pair
    {
      [$1]
    }
|   simple_expr_pair_list SEMICOLON simple_expr_pair
  {
    $1@[$3]
  }
;

simple_expr_pair :
  simple_expression COLON expression
     {
       let t:(Ast.sexpr_pair) = SExpr_pair ($1,$3) in t
     }
;
stream_generator :
  STREAM type_name LBRACK RBRACK
    {
      let t:(Ast.simple_exp) = Stream_generator ($2) in t
    }
| STREAM type_name LBRACK expression RBRACK
  {
    let t:(Ast.simple_exp) = Stream_generator_exp ($2,$4) in t
  }
| STREAM LBRACK expression RBRACK
  {
    let t:(Ast.simple_exp) = Stream_generator_unknown_exp $3 in t
  }
;

record_ref :
  primary DOTSTOP field_name
    {
      let t:(Ast.simple_exp) = Record_ref ($1,$3) in t
    }
;

record_generator :
  RECORD type_name LBRACK field_def_list RBRACK
    {
      let t:Ast.simple_exp =
        Record_generator_named ($2,$4) in t
    }
|  RECORD type_name LBRACK field_def_list SEMICOLON RBRACK
  {
    let t:Ast.simple_exp =
      Record_generator_named ($2,$4) in t
  }
|   RECORD LBRACK field_def_list RBRACK
  {
    let t:Ast.simple_exp =
      Record_generator_unnamed $3 in t
  }
|  RECORD LBRACK field_def_list SEMICOLON RBRACK
  {
    let t:Ast.simple_exp =
      Record_generator_unnamed $3 in t
  }
|  primary REPLACE LBRACK field_list RBRACK
  {
    let t:Ast.simple_exp =
      Record_generator_primary ($1, $4) in t
  }
|  primary REPLACE LBRACK field_list SEMICOLON RBRACK
  {
    let t:Ast.simple_exp =
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

field_def : field_name COLON simple_expression
    {
      let k:Ast.field_def = Field_def ($1,$3) in k
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
  field COLON simple_expression
    {
      let k:Ast.field_exp = Field_exp (Field $1,$3) in k
    }
;

tagcase_exp :
  TAGCASE simple_expression tag_list_colon_expression_list END TAGCASE
    {
      let t:(Ast.simple_exp) =
        Tagcase (Tagcase_exp $2, $3, Otherwise Empty) in t
    }
| TAGCASE simple_expression tag_list_colon_expression_list OTHERWISE COLON expression END TAGCASE
  {
    let t:(Ast.simple_exp) =
      Tagcase (Tagcase_exp $2, $3, Otherwise $6) in t
  }
| TAGCASE value_name ASSIGN simple_expression tag_list_colon_expression_list END TAGCASE
  {
    let t:(Ast.simple_exp) =
      Tagcase (Assign (Value_name $2,$4), $5, Otherwise Empty) in t
  }
| TAGCASE value_name ASSIGN simple_expression tag_list_colon_expression_list
  OTHERWISE COLON expression END TAGCASE
  {
    let t:(Ast.simple_exp) =
      Tagcase (Assign (Value_name $2, $4), $5, Otherwise $8) in t
  }
;

tag_list_colon_expression_list :
tag_list_colon_expression
  {
        [$1]
  }
| tag_list_colon_expression_list  tag_list_colon_expression
  {
    $1@[$2]
  }
;

tag_list_colon_expression :
  tagnames COLON expression
    {
      let t:(Ast.tagnames_colon_exp) =
        Tag_list ($1,$3) in t
    }
;

tagnames : TAG names
    {
      let t:Ast.tagnames =
      Tagnames $2 in t
    }
;

primary :
  constant
    {
      let t:Ast.simple_exp = Constant $1
      in t
    }
|   OLD value_name
  {
    let t:Ast.simple_exp = Old (Value_name $2) in t
  }
|   value_name
  {
    let t:Ast.simple_exp = Val (Value_name $1) in t
  }
|   LPAREN expression RPAREN
  {
    let t:Ast.simple_exp = Paren $2 in t
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
      let t:Ast.simple_exp =
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
      let t:Ast.simple_exp =
        For_initial (Decldef_part $3,$5,$7) in t
    }
| FOR
  in_exp_list
  RETURNS
  return_exp_list
  END FOR
  {
    let t:Ast.simple_exp =
      For_all ($2,Decldef_part [],$4) in t
  }

| FOR
  in_exp_list
  decldef_part
  RETURNS
  return_exp_list
  END FOR
  {
    let t:Ast.simple_exp =
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
    let t:Ast.simple_exp =
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
      let t:(Ast.iterator) =
      Repeat $2 in t
    }
;

termination_test :
  WHILE expression
    {
      let t:(Ast.termination_test) =
      While $2 in t
    }
|   UNTIL expression
  {
    let t:(Ast.termination_test) =
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
      let t:(Ast.in_exp) =
      Dot($1,$3) in t
    }
| in_exp_list CROSS in_exp
    {
      let t:(Ast.in_exp) =
      Cross ($3,$1) in t
    }
| in_exp
    {
       $1
    }
;

in_exp:
  NAME IN expression
    {
      let t:(Ast.in_exp) =
        In_exp (Value_name $1, $3) in t
    }
|   in_exp AT names
  {
    let t:(Ast.in_exp) =
      At_exp ($1, Value_names $3) in t
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
  UNLESS simple_expression
    {
      Unless $2
    }
|   WHEN simple_expression
  {
    let t:(Ast.masking_clause) = When $2 in t
  }
;

return_exp:
  VALUE OF direction simple_expression
    {
      let t:(Ast.return_exp) = Value_of ($3, No_red, $4)
      in t
    }
|   VALUE OF direction reduction_op simple_expression
  {
    let t:(Ast.return_exp) = Value_of ( $3, $4, $5)
    in t
  }
|   VALUE OF reduction_op simple_expression
  {
    let t:(Ast.return_exp) = Value_of (No_dir, $3, $4)
    in t
  }
|   VALUE OF simple_expression
  {
    let t:(Ast.return_exp) =
      Value_of (No_dir,No_red,$3) in t
  }
|   ARRAY OF simple_expression
  {
    let t:(Ast.return_exp) = Array_of $3 in t
  }
|   STREAM OF simple_expression
  {
    let t:(Ast.return_exp) = Stream_of $3 in t
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
    let t:Ast.direction_op = Tree in t
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
    let t:Ast.reduction_op = Catenate in t
  }
;

conditional_exp:
  conditional_ifexp conditional_else END IF
  {
    let t:(Ast.simple_exp) = If ([$1],$2) in t
  }
|   conditional_ifexp conditional_elseif conditional_else END IF
  {
    let t:(Ast.simple_exp) = If ($1::$2,$3) in t
  }
;

conditional_elseif:
  ELSEIF expression THEN expression
    {
      let t:(Ast.cond) =
        Cond ($2,$4) in [t]
    }
|   conditional_elseif ELSEIF expression THEN expression
  {
    $1@[let t:(Ast.cond) = Cond ($3,$5) in t]
  }
;

conditional_else:
ELSE expression
  {
    let t:(Ast.last_else) = Else $2 in t
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
      let t:(Ast.simple_exp) = Is ($2,$4) in t
    }
;
union_generator :
  UNION type_name LBRACK tag_name RBRACK
    {
      let t:Ast.simple_exp = Union_generator ($2,Tag_name $4) in t
    }
| UNION type_name LBRACK tag_name COLON simple_expression RBRACK
  {
    let t:Ast.simple_exp = Union_generator ($2,Tag_exp ($4,$6)) in t
  }
;
error_test :
  IS ERROR LPAREN expression RPAREN
    {
      let t:Ast.simple_exp = Is_error $4 in t
    }
;
  tag_name : NAME
    {
      let t:Ast.tag_name = $1 in t
    }
;

prefix_operation :
  prefix_name LPAREN expression RPAREN
    {
      let k:Ast.simple_exp =
       Prefix_operation ($1,$3) in k
    }
;
  prefix_name :
  CHARACTER
    {
      let k:Ast.prefix_name = Char_prefix in k
    }
| DOUBLE_REAL
  {
      let k:Ast.prefix_name = Double_prefix in k
  }
| INTEGER
  {
      let k:Ast.prefix_name = Integer_prefix in k
  }
| REAL
  {
      let k:Ast.prefix_name = Real_prefix in k
  }
;

constant : FALSE
    {
      let k:Ast.sisal_constant = False in k
    }
| NIL
  {
    let k:Ast.sisal_constant = Nil in k
  }
| TRUE
  {
    let k:Ast.sisal_constant = True in k
  }
| INT
  {
    let k:Ast.sisal_constant = Int $1 in k
  }
| FLOAT
  {
    let k:Ast.sisal_constant = Float $1 in k
  }
| CHAR
  {
    let k:Ast.sisal_constant = Char $1 in k
  }
| STRING
  {
    let k:Ast.sisal_constant = String $1 in k
  }
| ERROR LBRACK type_spec RBRACK
  {
    let k:Ast.sisal_constant = Error $3 in k
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
      let k:Ast.type_def = Type_def ($2, $4)
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
      let k:Ast.sisal_type = Boolean in k
    }
| CHARACTER
    {
      let k:Ast.sisal_type = Character in k
    }
| DOUBLE_REAL
  {
      let k:Ast.sisal_type = Double_real in k
  }
| INTEGER
  {
      let k:Ast.sisal_type = Integer in k
  }
| NULL
  {
    let k:Ast.sisal_type = Null in k
  }
| REAL
  {
      let k:Ast.sisal_type = Real in k
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

declids_spec_list :
  | declids_spec_list SEMICOLON declids COLON type_spec
      {
        $1@[($3, $5)]
      }
  | declids COLON type_spec
      {
        [($1, $3)]
      }
;

compound_type_spec :
  ARRAY LBRACK type_spec RBRACK
    {
      let k:Ast.compound_type = Sisal_array $3 in k
    }
|   STREAM LBRACK type_spec RBRACK
  {
      let k:Ast.compound_type = Sisal_stream $3 in k
  }
|   RECORD LBRACK tag_spec_list RBRACK
  {
      let k:Ast.compound_type = Sisal_record $3 in k
  }
|   UNION LBRACK tag_spec_list RBRACK
  {
      let k:Ast.compound_type = Sisal_union $3 in k
  }
|   UNION LBRACK names RBRACK
  {
      let k:Ast.compound_type = Sisal_union_enum $3 in k
  }
;

tag_spec_list :
  | tag_spec_list SEMICOLON names COLON type_spec
      {
        $1@[($3, $5)]
      }
  | names COLON type_spec
      {
        [($1, $3)]
      }
;

declids :
 function_header
   {
     (*TODO*)
      [Decl_func $1]
    }
| NAME
    {
      [Decl_name $1]
    }
| declids COMMA NAME
    {
      $1@[Decl_name $3]
    }
| declids COMMA function_header
    {
      $1@[Decl_func $3]
    }
;

decldef :
  declids_list ASSIGN expression
    {
      (*TODO decldef can contain a list of declids COLON type_specs*)
      let t:(Ast.decldef) = Decldef ($1, $3) in t
    }
  |
    declids ASSIGN expression
      {
        let t:(Ast.decldef) = Decldef ([Decl_none $1], $3) in t
      }
;

declids_list :
  | declids_list COMMA declids COLON type_spec
      {
        $1@[Decl_some ($3, $5)]
      }

  | declids COLON type_spec
      {
        (Decl_some ($1, $3))::[]
      }

;

decldef_part :
  decldef
    {
      [$1]
    }
  | decldef_part SEMICOLON decldef
    {
      $1@[$3]
    }
  | decldef_part ANDKW decldef
      {
        $1@[$3]
      }
;

let_in_exp :
  LET decldef_part IN expression END LET
    {
      let t:Ast.simple_exp = Let (Decldef_part $2, $4) in t
    }
  | LET REC decldef_part IN expression END LET
    {
      let t:Ast.simple_exp = Let_rec (Decldef_part $3, $5) in t
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
      let t:(Ast.simple_exp) =
        Invocation ($1,Arg Empty) in t
    }
|   function_name LPAREN expression RPAREN
  {
    let t:(Ast.simple_exp) =
      Invocation ($1,Arg $3) in t
  }
;
function_name : NAME
    {
      let t:(Ast.function_name) =
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
    let k:Ast.field_name = Field_name $1
    in k
  }
;

main: compilation_unit
  {
    $1
  }
;
