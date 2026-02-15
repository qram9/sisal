%{

open Ir.Ast
     (*open Lexing*)
     (*open Parsing*)
  let debug_level = ref 3

let parse_msg level fmt =
  let print_at_level str = 
    if !debug_level >= level then (print_string str; print_newline ()) 
  in
  Format.ksprintf print_at_level fmt
     %}

%token AS
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
%token<int> BYTE
%token<int> UBYTE
%token<int> UCHAR
%token<int> UINT
%token<int> SHORT
%token<int> USHORT
%token<float> FLOAT
%token<float> DOUBLE
%token<float> HALF
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
%token USING
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
%token UINT_TY
%token BYTE_TY
%token HALF_TY
%token SHORT_TY
%token USHORT_TY
%token UBYTE_TY
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
%token BYTE2_TY
%token CHAR2_TY
%token HALF2_TY
%token SHORT2_TY
%token INT2_TY
%token FLOAT2_TY
%token DOUBLE2_TY
%token UINT2_TY
%token UBYTE2_TY
%token USHORT2_TY
%token BYTE3_TY
%token CHAR3_TY
%token HALF3_TY
%token SHORT3_TY
%token INT3_TY
%token FLOAT3_TY
%token DOUBLE3_TY
%token UINT3_TY
%token UBYTE3_TY
%token USHORT3_TY
%token BYTE4_TY
%token CHAR4_TY
%token HALF4_TY
%token SHORT4_TY
%token INT4_TY
%token FLOAT4_TY
%token DOUBLE4_TY
%token UINT4_TY
%token UBYTE4_TY
%token USHORT4_TY
%token BYTE8_TY
%token CHAR8_TY
%token HALF8_TY
%token SHORT8_TY
%token INT8_TY
%token FLOAT8_TY
%token DOUBLE8_TY
%token UINT8_TY
%token UBYTE8_TY
%token USHORT8_TY
%token BYTE16_TY
%token CHAR16_TY
%token HALF16_TY
%token SHORT16_TY
%token INT16_TY
%token FLOAT16_TY
%token DOUBLE16_TY
%token UINT16_TY
%token UBYTE16_TY
%token USHORT16_TY
%token MAT2_TY
%token MAT3_TY
%token MAT4_TY
/* Lowest Precedence */
%left PIPE OR           /* Logical OR / Bitwise OR */
%left AND               /* Logical AND / Bitwise AND */
%left LT GT EQ NE LE GE /* Comparisons must happen AFTER arithmetic but BEFORE logic */
%left PLUS MINUS        /* Addition/Subtraction */
%left STAR DIVIDE       /* Multiplication/Division */
%left UMINUS            /* Unary Minus (e.g., -eel) */
%left DOTSTOP           /* Swizzle/Record Access */
/* Highest Precedence */
%type <Ir.Ast.compilation_unit> main
%start main
%%

 /* 1. Our individual import (e.g., "lib.sis" AS Math) */
using_item:
  | s = STRING               { (s, None) }
  | s = STRING AS n = NAME   { (s, Some n) }

/* 2. Our comma-separated list (e.g., "a.sis", "b.sis" AS B) */
using_decl_list:
  | item = using_item                         { [item] }
  | rest = using_decl_list COMMA item = using_item { item :: rest }

/* 3. Our actual statement that appears in the top_fragment */
using_stmt:
  | USING decls = using_decl_list SEMICOLON { List.rev decls }

/* 4. Integrating into our Fragment list */
top_fragment:
  | u = using_stmt          { F_Using  (Using u) }
  | d = def_func_name_list  { F_Define d }
  | t = type_def_part       { F_Types (List.rev t) }
  | g = global_header_list  { F_Globals (List.rev g) }
  | f = function_def_list   { F_Functions (List.rev f) }
  | SEMICOLON               { F_Skip }
  ;

/* 5. Build the list (Menhir handles the recursion) */
top_fragment_list:
  | frag = top_fragment { [frag] }
  | rest = top_fragment_list frag = top_fragment { frag :: rest }

/* 6. The New Unified Entry Point */
compilation_unit:
  | frags = top_fragment_list EOF 
    { 
      Compilation_unit (List.rev frags) 
    }
    ;

global_header_list :
    GLOBAL function_header
      { [$2] }
| global_header_list GLOBAL function_header
    { $3 :: $1 }
  ;
def_func_name_list:
    DEFINE function_name_list
      { Define (List.rev $2) }
  ;
function_name_list :
    function_name_list NAME
      { (Function_name [$2]) :: $1 }
| NAME
    { [Function_name [$1]] }
  ;

  function_def_list: function_def
      { [$1] }
| function_def_list function_def
    { $2 :: $1 }
  ;

  function_def:
    FORWARD FUNCTION function_header
      { Forward_function $3 }
| function_nest
    { Function $1 }
  ;

  function_nest:
    FUNCTION function_header function_nest expression END FUNCTION
      { let t =
          ($2,[],$3,$4)
        in [Function_single t] }
|   FUNCTION function_header type_def_part opt_semicolon function_nest expression END FUNCTION
    { let t =
        ($2,$3,$5,$6)
      in [Function_single t] }

| FUNCTION function_header expression END FUNCTION
    { let t =
        ($2,[],[],$3)
      in [Function_single t] }
|   FUNCTION function_header type_def_part opt_semicolon expression END FUNCTION
    { let t =
        ($2,$3,[],$5)
      in [Function_single t] }

  ;

  function_header :
    function_name LPAREN RETURNS type_list RPAREN
      { Function_header_nodec ($1, List.rev $4) }
| function_name LPAREN declids_spec_list RETURNS type_list RPAREN
    { let wrapped = List.map (fun (x,y) -> Decl_with_type (x,y) ) (List.rev $3) in
      Function_header ($1, wrapped, List.rev $5) }
  ;

  type_list :
    type_spec
      { [$1] }
|   type_list COMMA type_spec
    { $3 :: $1 }
  ;
  expression: exp_list
      { Exp (List.rev $1) }
  ;
  exp_list :
    simple_expression
      { [$1] }
|  exp_list COMMA simple_expression
    { $3 :: $1 }
  ;
  opt_semicolon:
    |         /* empty */ { ()  }
| SEMICOLON   { ()  }

    simple_expression:
    primary_part2
      { $1
      }
| simple_expression   GT simple_expression
    { Greater ($1,$3) }
| simple_expression   GE simple_expression
    { Greater_equal($1,$3) }
| simple_expression
    LT
    simple_expression
    { Lesser ($1,$3) }
| simple_expression
    LE
    simple_expression
    { Lesser_equal ($1,$3) }

| simple_expression
    EQ
    simple_expression
    { Equal($1,$3) }

| simple_expression
    NE
    simple_expression
    { Not_equal ($1,$3) }

| simple_expression
    PLUS
    simple_expression
    { Add ($1,$3) }

| simple_expression
    MINUS
    simple_expression
    { Subtract ($1,$3) }

| simple_expression
    OR
    simple_expression
    { Or ($1,$3) }

| simple_expression
    STAR
    simple_expression
    { Multiply ($1,$3) }
| simple_expression
    DIVIDE
    simple_expression
    { Divide ($1,$3) }
| simple_expression
    AND
    simple_expression
    { And ($1,$3) }
| simple_expression
    PIPE
    simple_expression
    { Pipe ($1, $3) }
|  PLUS simple_expression
    { $2 }
|   MINUS simple_expression %prec UMINUS
      { Negate $2 }
|   NOT simple_expression %prec UMINUS
      { Not $2 }

  ;

  primary_part2 :
    primary
      { $1 }
|  array_ref
    { $1 }
  /* --- 2. Vector & Matrix Constructors --- */

| v = vec_type LPAREN e = expression RPAREN 
    { 
      let args_list = match e with
        | Exp el -> el
        | Empty  -> 
            let _ = parse_msg 1 "Error: Vector/Matrix constructors cannot be empty" in
            raise Parsing.Parse_error 
      in
      (* Convert simple_exp list to exp list by wrapping each in Exp container *)
      let boxed_args = List.map (fun s -> Exp [s]) args_list in
      Vec(v, boxed_args)
    }

| m = mat_type LPAREN e = expression RPAREN 
    { 
      let args_list = match e with
        | Exp el -> el
        | Empty  -> 
            let _ = parse_msg 1 "Error: Matrix constructors cannot be empty" in
            raise Parsing.Parse_error 
      in
      let boxed_args = List.map (fun s -> Exp [s]) args_list in
      Mat(m, boxed_args)
    }

|   array_generator
    { $1 }
|   stream_generator
    { $1 }
|   record_ref
    { $1 }
|   record_generator
    { $1 }
|   union_test
    { $1 }
|   union_generator
    { $1 }
|   error_test
    { $1 }
|   prefix_operation
    { $1 }
|   conditional_exp
    { $1 }
|   let_in_exp
    { $1 }
|   tagcase_exp
    { $1 }
|   iteration_exp
    { $1 }

  array_ref :
    primary LBRACK expression RBRACK
      { Array_ref ($1,$3)  }
  ;

  array_generator :
    ARRAY type_name LBRACK RBRACK
      { Array_generator_named $2 }
|    ARRAY LBRACK simple_expr_pair RBRACK
    { Array_generator_unnamed $3 }
|    ARRAY type_name LBRACK simple_expr_pair RBRACK
    { Array_generator_named_addr ($2,$4) }
|    primary LBRACK simple_expr_pair_list opt_semicolon RBRACK
    { Array_replace ($1, List.rev $3) }

  ;

  simple_expr_pair_list :
    simple_expr_pair
      { [$1] }
|   simple_expr_pair_list SEMICOLON simple_expr_pair
    { $3 :: $1 }
  ;

  simple_expr_pair :
    simple_expression COLON expression
      { SExpr_pair ($1,$3) }
  ;
  stream_generator :
    STREAM type_name LBRACK RBRACK
      { Stream_generator ($2) }
| STREAM type_name LBRACK expression RBRACK
    { Stream_generator_exp ($2,$4) }
| STREAM LBRACK expression RBRACK
    { Stream_generator_unknown_exp $3 }
  ;

  record_ref :
    simple_expression DOTSTOP field_name
      { Record_ref ($1,$3) }
| record_ref DOTSTOP field_name { Record_ref($1, $3) }
  ;

  record_generator :
    RECORD type_name LBRACK field_def_list opt_semicolon RBRACK
      { Record_generator_named ($2, List.rev $4)  }
|  RECORD LBRACK field_def_list opt_semicolon RBRACK
    { Record_generator_unnamed (List.rev $3)  }
|  primary REPLACE LBRACK field_list opt_semicolon RBRACK
    { Record_generator_primary ($1, (List.rev $4))  }
  ;

  field_def_list :
    field_def
      { [$1] }
| field_def_list SEMICOLON field_def
    { $3 :: $1 }
  ;

  field_def : field_name COLON simple_expression
      { Field_def ($1,$3) }
  ;
  field_list :
    field_expn
      { [$1] }
|   field_list SEMICOLON field_expn
    { $3 :: $1 }
  ;
  field_expn :
    field COLON simple_expression
      { Field_exp (Field (List.rev $1),$3) }
  ;

  tagcase_exp :
    TAGCASE simple_expression tag_list_colon_expression_list END TAGCASE
      { Tagcase (Tagcase_exp $2, List.rev $3, Otherwise Empty)  }
| TAGCASE simple_expression tag_list_colon_expression_list OTHERWISE COLON expression END TAGCASE
    { Tagcase (Tagcase_exp $2, List.rev $3, Otherwise $6)  }
| TAGCASE value_name ASSIGN simple_expression tag_list_colon_expression_list END TAGCASE
    { Tagcase (Assign (Value_name [$2],$4), List.rev $5, Otherwise Empty)  }
| TAGCASE value_name ASSIGN simple_expression tag_list_colon_expression_list
    OTHERWISE COLON expression END TAGCASE
    { Tagcase (Assign (Value_name [$2], $4), List.rev $5, Otherwise $8)  }
  ;

  tag_list_colon_expression_list :
    tag_list_colon_expression
      { [$1] }
| tag_list_colon_expression_list  tag_list_colon_expression
    { $2 :: $1 }
  ;

  tag_list_colon_expression :
    tagnames COLON expression
      { Tag_list ($1,$3) }
  ;

  tagnames : TAG names
      { Tagnames (List.rev $2)  }
  ;

  primary :
    constant
      { Constant $1 }
|   OLD value_name
    { Old (Value_name [$2]) }
|   value_name
    {Val (Value_name [$1]) }
|   LPAREN expression RPAREN
    { Paren $2  }
|   invocation
    {  $1 }
  ;

  iteration_exp:
    FOR
      INITIAL
      decldef_part
      iterator_terminator
      RETURNS return_exp_list
      END FOR
      { For_initial (Decldef_part (List.rev $3), $4, (List.rev $6)) }
| FOR
    INITIAL
    decldef_part
    SEMICOLON
    iterator_terminator
    RETURNS return_exp_list
    END FOR
    { For_initial (Decldef_part (List.rev $3), $5, List.rev $7) }
| FOR
    in_exp_list
    RETURNS
    return_exp_list
    END FOR
    { For_all ($2,Decldef_part [], List.rev $4) }

| FOR
    in_exp_list
    decldef_part
    RETURNS
    return_exp_list
    END FOR
    { For_all ($2,Decldef_part (List.rev $3), List.rev $5)  }
|   FOR
    in_exp_list
    decldef_part
    SEMICOLON
    RETURNS
    return_exp_list
    END FOR
    { For_all ($2,Decldef_part (List.rev $3), List.rev $6) }
  ;

  iterator_terminator:
    iterator termination_test
      { Iterator_termination ($1,$2) }
|   termination_test iterator
    { Termination_iterator ($1,$2) }
  ;

  iterator:
    REPEAT iterator_body
      { Repeat $2 }
  ;

  termination_test :
    WHILE expression
      { While $2 }
|   UNTIL expression
    { Until $2 }
  ;

  iterator_body :
    decldef_part opt_semicolon
      { Decldef_part (List.rev $1) }

  ;

  in_exp_list: in_exp_list DOT in_exp
      { Dot($1,$3) }
| in_exp_list CROSS in_exp
    { Cross ($1,$3) }
| in_exp
    { $1 }
  ;

  in_exp:
    NAME IN expression
      { In_exp (Value_name [$1], $3) }
|   in_exp AT names
    { At_exp ($1, Value_names (List.rev $3)) }
  ;

  return_exp_list:
    return_exp_list return_clause
      { $2 :: $1 }
|   return_clause_old
    { [$1] }
|   return_clause
    { [$1] }
  ;
  return_clause_old:
    OLD return_exp masking_clause
      { Old_ret  ($2, $3) }
|   OLD return_exp
    { Old_ret ($2, No_mask) }
  ;
  return_clause:
    return_exp masking_clause
      { Return_exp ($1, $2) }
|   return_exp
    { Return_exp ($1, No_mask)  }
  ;
  masking_clause:
    UNLESS simple_expression
      { Unless $2 }
|   WHEN simple_expression
    { When $2 }
  ;

  return_exp:
    VALUE OF direction simple_expression
      { Value_of ($3, No_red, $4) }
|   VALUE OF direction reduction_op simple_expression
    { Value_of ( $3, $4, $5) }
|   VALUE OF reduction_op simple_expression
    { Value_of (No_dir, $3, $4) }
|   VALUE OF simple_expression
    { Value_of (No_dir,No_red,$3) }
|   ARRAY OF simple_expression
    { Array_of $3 }
|   STREAM OF simple_expression
    { Stream_of $3 }
  ;

  direction:
    LEFT
      { Left }
|   RIGHT
    { Right }
|   TREE
    { Tree }
  ;
  reduction_op:
    SUM
      { Sum }
|   PRODUCT
    { Product }
|   LEAST
    { Least }
|   GREATEST
    { Greatest }
|   CATENATE
    { Catenate  }
  ;

  conditional_exp:
    conditional_ifexp conditional_else END IF
      { If ([$1],$2) }
|   conditional_ifexp conditional_elseif conditional_else END IF
    { If ($1::(List.rev $2),$3) }
  ;

  conditional_elseif:
    ELSEIF expression THEN expression
      { [Cond ($2,$4)] }
|   conditional_elseif ELSEIF expression THEN expression
    { Cond ($3,$5) :: $1 }
  ;

  conditional_else:
ELSE expression
  { Else $2 }
;

conditional_ifexp:
  IF expression THEN expression
    { Cond ($2,$4) }
;

union_test :
  IS tag_name LPAREN expression RPAREN
    { Is ($2,$4) }
;
union_generator :
  UNION type_name LBRACK tag_name RBRACK
    { Union_generator ($2,Tag_name $4) }
| UNION type_name LBRACK tag_name COLON simple_expression RBRACK
  { Union_generator ($2,Tag_exp ($4,$6))  }
;
error_test :
  IS ERROR LPAREN expression RPAREN
    { Is_error $4 }
;
tag_name : NAME
    { $1 }
;

prefix_operation :
  prefix_name LPAREN expression RPAREN
    { Prefix_operation ($1,$3) }
;
prefix_name :
  CHARACTER
    { Char_prefix }
| DOUBLE_REAL
  { Double_prefix }
| INTEGER
  { Integer_prefix }
| REAL
  { Real_prefix }
        | UINT {Uint_prefix }
        | SHORT {Short_prefix }
        | USHORT {Ushort_prefix }
        | BYTE {Byte_prefix}
        | UBYTE {Ubyte_prefix}
        | HALF {Half_prefix}
        | UCHAR {Uchar_prefix}
;

constant : FALSE
    { False }
| NIL
  { Nil }
| TRUE
  { True }
| INT
  { Int $1 }
| FLOAT
  { Float $1 }
| UINT
  { Uint $1 }
| BYTE
  { Byte $1 }
| UBYTE
  { Ubyte $1}
| SHORT
  { Short $1}
| USHORT
   { Ushort $1 }
| CHAR
  { Char $1 }
| UCHAR
  { Uchar $1 }
| STRING
  { String $1 }
| ERROR LBRACK type_spec RBRACK
  { Error $3 }
;

type_def_part: type_def
    { [$1] }
|   type_def_part SEMICOLON type_def
  { $3 :: $1 }
;
type_def : TYPE type_name EQ type_spec opt_semicolon
    { Type_def ($2, $4) }
;
type_spec : basic_type_spec
    { $1 }
|   compound_type_spec
  { Compound_type $1 }
|   type_name
  { Type_name $1  }
|   v = vec_type 
    { Vec_ty v }
|   m = mat_type 
    { Mat_ty m }
;

type_name : NAME
    { $1  }
;

basic_type_spec :
  BOOLEAN         { Boolean }
| CHARACTER       { Character }
| DOUBLE_REAL     { Double_real }
| INTEGER         { Integer }
| NULL            { Null }
| REAL            { Real }
| BYTE_TY            { Byte_ty}
| HALF_TY            { Half_ty }
| UINT_TY            { Uint_ty }
| SHORT_TY           { Short_ty }
| USHORT_TY          { Ushort_ty }
| UBYTE_TY           { Ubyte_ty }
| DOUBLE          { Double_real } 
;

mat_type:
        | MAT2_TY { Mat2 }
        | MAT3_TY { Mat3}
        | MAT4_TY { Mat4}
;

vec_type:
  | BYTE2_TY    { Byte2 }   | BYTE3_TY    { Byte3 }   | BYTE4_TY    { Byte4 }
  | BYTE8_TY    { Byte8 }   | BYTE16_TY   { Byte16 }
  | CHAR2_TY    { Char2 }   | CHAR3_TY    { Char3 }   | CHAR4_TY    { Char4 }
  | CHAR8_TY    { Char8 }   | CHAR16_TY   { Char16 }
  | HALF2_TY    { Half2 }   | HALF3_TY    { Half3 }   | HALF4_TY    { Half4 }
  | HALF8_TY    { Half8 }   | HALF16_TY   { Half16 }
  | SHORT2_TY   { Short2 }  | SHORT3_TY   { Short3 }  | SHORT4_TY   { Short4 }
  | SHORT8_TY   { Short8 }  | SHORT16_TY  { Short16 }
  | INT2_TY     { Int2 }    | INT3_TY     { Int3 }    | INT4_TY     { Int4 }
  | INT8_TY     { Int8 }    | INT16_TY    { Int16 }
  | FLOAT2_TY   { Float2 }  | FLOAT3_TY   { Float3 }  | FLOAT4_TY   { Float4 }
  | FLOAT8_TY   { Float8 }  | FLOAT16_TY  { Float16 }
  | DOUBLE2_TY  { Double2 } | DOUBLE3_TY  { Double3 } | DOUBLE4_TY  { Double4 }
  | DOUBLE8_TY  { Double8 } | DOUBLE16_TY { Double16 }
  | UINT2_TY    { Uint2 }   | UINT3_TY    { Uint3 }   | UINT4_TY    { Uint4 }
  | UINT8_TY    { Uint8 }   | UINT16_TY   { Uint16 }
  | UBYTE2_TY   { Ubyte2 }  | UBYTE3_TY   { Ubyte3 }  | UBYTE4_TY   { Ubyte4 }
  | UBYTE8_TY   { Ubyte8 }  | UBYTE16_TY  { Ubyte16 }
  | USHORT2_TY  { Ushort2 } | USHORT3_TY  { Ushort3 } | USHORT4_TY  { Ushort4 }
  | USHORT8_TY  { Ushort8 } | USHORT16_TY { Ushort16 }
;
names : names COMMA NAME
    { $3 :: $1 }
|   NAME
  { [$1] }
;

declids_spec_list :
  | declids_spec_list SEMICOLON declids COLON type_spec
    { (List.rev $3, $5) :: $1 }
| declids COLON type_spec
  { [(List.rev $1, $3)] }
;

compound_type_spec :
  ARRAY LBRACK type_spec RBRACK
    { Sisal_array $3 }
|   STREAM LBRACK type_spec RBRACK
  { Sisal_stream $3 }
|   RECORD LBRACK tag_spec_list RBRACK
  { Sisal_record (List.rev $3) }
|   UNION LBRACK tag_spec_list RBRACK
  { Sisal_union (List.rev $3) }
|   UNION LBRACK names RBRACK
  { Sisal_union_enum (List.rev $3) }
;

tag_spec_list :
  | tag_spec_list SEMICOLON names COLON type_spec
    { ($3, $5) :: $1 }
| names COLON type_spec
  { [($1, $3)] }
;

declids :
  function_header
    { (*TODO*)
      [Decl_func $1] }
| NAME
  { [Decl_name $1] }
| declids COMMA NAME
  { (Decl_name $3) :: $1 }
| declids COMMA function_header
  { (Decl_func $3) :: $1 }
;

decldef :
  declids_list ASSIGN expression
    { (*TODO decldef can contain a list of declids COLON type_specs*)
      Decldef ($1, $3) }
|
declids ASSIGN expression
  { Decldef ([Decl_no_type (List.rev $1)], $3) }
;

declids_list :
  | declids_list COMMA declids COLON type_spec
    { Decl_with_type (List.rev $3, $5) :: (List.rev $1) }

| declids COLON type_spec
  { [Decl_with_type (List.rev $1, $3)] }

;

decldef_part :
  decldef
    { [$1] }
| decldef_part SEMICOLON decldef
  { $3 :: $1 }
| decldef_part ANDKW decldef
  { $3 :: $1 }
;

let_in_exp :
  LET decldef_part IN expression END LET
    { Let (Decldef_part (List.rev $2), $4) }
| LET REC decldef_part IN expression END LET
  { Let_rec (Decldef_part (List.rev $3), $5) }
;

value_name : NAME
    { $1 }
;

invocation :
  function_name LPAREN RPAREN
    { Invocation ($1,Arg Empty)  }
|   function_name LPAREN expression RPAREN
  { Invocation ($1,Arg $3) }
;
function_name : NAME
    { Function_name [$1]  }
;
field : field_name
    { [$1] }
| field DOTSTOP field_name
  { $3 :: $1 }
;

field_name : NAME
    { Field_name $1 }
;

main: compilation_unit
    { $1 }
;
