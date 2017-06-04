let mysplcon a b cha =
match b with 
| "" -> a
| _ -> (match a with 
  | "" -> b
  | _ -> a ^ cha ^ b)

type field_spec =
   Field_spec of string list * sisal_type
and
field =
   Field of field_name list
and field_name = Field_name of string
and
  field_exp = Field_exp of field * exp
and
  field_def = Field_def of field_name * exp
and expr_pair = Expr_pair of exp * exp
and type_def = Type_def of type_name * sisal_type
and tag_exp = Tag_name of tag_name | Tag_exp of tag_name * exp
and iterator_terminator = Iterator_termination of iterator * termination_test
                          | Termination_iterator of termination_test * iterator
and iterator = Repeat of decldef_part
and termination_test = While of exp | Until of exp
and decldef = Def of string list * exp
              | Decl of string list * sisal_type 
              | Decldef of decldef list * exp
and simple_exp =
  Constant of sisal_constant
  | Old of value_name
  | Val of value_name
  | Paren of exp
  | Invocation of function_name * arg
  | Array_ref of simple_exp * exp
  | Array_generator_named of type_name
  | Array_generator_unnamed of expr_pair
  | Array_generator_named_addr of type_name * expr_pair
  | Array_generator_primary of simple_exp * expr_pair list
  | Stream_generator of type_name
  | Stream_generator_exp of type_name * exp
  | Record_ref of simple_exp * field_name
  | Record_generator_named of type_name * field_def list
  | Record_generator_unnamed of field_def list
  | Record_generator_primary of simple_exp * field_exp list
  | Is of tag_name * exp
  | Union of type_name * tag_exp
  | Is_error of exp
  | Prefix_operation of prefix_name * exp
  | If of (cond list) * last_else 
  | Let of decldef_part * exp
  | Tagcase of
      assign_exp * tagnames_colon_exp * otherwise
  | For_all of in_exp * decldef_part * (return_clause list)
  | For_initial of decldef_part * iterator_terminator * (return_clause list)
  | Not of simple_exp
  | Negate of simple_exp
  | Pipe of  simple_exp * simple_exp
  | And of simple_exp * simple_exp
  | Divide of simple_exp * simple_exp
  | Multiply of simple_exp * simple_exp
  | Or of simple_exp * simple_exp
  | Subtract of simple_exp * simple_exp
  | Add of simple_exp * simple_exp
  | Not_equal of simple_exp * simple_exp
  | Equal of simple_exp * simple_exp
  | Lesser_equal of simple_exp * simple_exp
  | Lesser of simple_exp * simple_exp
  | Greater_equal of simple_exp * simple_exp
  | Greater of simple_exp * simple_exp 
and exp = Exp of simple_exp list | Nil
and cond = Cond of exp * exp
and last_else = Else of exp
and otherwise = Otherwise of exp | Empty
and assign_exp = Assign of value_name * exp | Tagcase_exp of exp
and tagnames = Tagnames of string list
and tagnames_colon_exp = Tag_list of tagnames * exp
and arg = Empty | Arg of exp
and function_name = Function_name of string
and function_header = Function_header of function_name * decldef list * sisal_type list
                      | Function_header_nodec of function_name * sisal_type list
and function_def = Forward_function of function_header
               | Function of ((function_header * (type_def list)) list * exp)
and define = Define of function_name list
and compilation_unit = Compilation_unit of define * (type_def list) * (function_header list) * (function_def list)
and fun_returns = Returns of sisal_type list
and decldef_part = Decldef_part of decldef list
and reduction_op = Sum | Product | Least | Greatest | Catenate | Empty
and direction_op = Left | Right | Tree | Empty
and in_exp = In_exp of value_name * exp
             | At_exp of in_exp * value_name
             | Dot of in_exp * in_exp
             | Cross of in_exp * in_exp
and value_name = Value_name of string
and return_exp = Value_of of direction_op * reduction_op * exp
                    | Array_of of exp | Stream_of of exp
and masking_clause = Unless of exp | When of exp | Empty
and return_clause = Return_exp of return_exp * masking_clause
                       | Old of  return_exp * masking_clause
and
sisal_constant = 
  False | Nil | True | Int of int
  | Float of float | Char of string
  | String of string | Error of sisal_type 
and
  prefix_name = Char_prefix | Double_prefix | Integer_prefix | Real_prefix
and
  sisal_type = 
    Boolean
  | Character
  | Double_real
  | Integer
  | Null
  | Real
  | Compound_type of compound_type
  | Type_name of type_name
and
  compound_type =
  Sisal_array  of sisal_type
  | Sisal_stream of sisal_type
  | Sisal_record of (field_spec list)
  | Sisal_union  of (string list * sisal_type)
  | Sisal_union_enum  of (string list)
and tag_name = string
and type_name = string

(*
type array_value = { t : sisal_type ; lo : int; hi : int }
type stream_value = { t : sisal_type ; hi : int }

let rec 
  str_forall_loop fl = 
  match fl with
  | For (Inexp_list il, Returns_list rl) ->
    "FOR " ^ il ^ " RETURNS " ^ rl
and str_primary = function
  False -> "False"
  | Nil -> "Nil"
  | True -> "True"
  | Int ii -> string_of_int ii
  | Float ff -> string_of_float ff
  | Char cc -> cc
  | String st -> st
  | Error ts -> str_sisal_type ts
and str_sisal_type st =
  match st with 
  | Boolean -> "BOOLEAN"
  | Character -> "CHARACTER"
  | Double_real -> "DOUBLE_REAL"
  | Integer -> "INTEGER"
  | Null -> "NULL"
  | Real -> "REAL"
  | Type_name  t    -> t
  | Sisal_array  sa ->
    ("ARRAY"   ^ "[ " ^ (str_sisal_type  sa) ^ " ]")
  | Sisal_stream ss ->
    ("STREAM"  ^ "[ " ^ (str_sisal_type  ss) ^ " ]")
  | Sisal_record sr ->
    ("RECORD"  ^ "[ " ^ (foldf sr) ^ " ]")
  | Sisal_union su ->
    ("UNION"   ^ "[ " ^ (foldu su) ^ " ]")
and foldf sr = 
  (List.fold_left
     (fun last fs -> (mysplcon last (str_field fs) ";"))
     ""
     sr) 
and foldu su = 
  (List.fold_left
     (fun last fs -> (mysplcon last (str_tag fs) ";"))
     ""
     su) 
and
  str_field = function
  | Field (f,ts) ->
    match f with
    | Field_name af ->  
    (af ^ ":" ^ (str_sisal_type ts))
    | Field_names cdrf -> 
      (List.fold_left
        (fun last fs -> (mysplcon last fs ","))
        "" cdrf)
and
  str_tag = function
  | (t,ts) -> 
    let r =
      (List.fold_left
        (fun last fs -> (match fs with Tag f -> mysplcon last f ","))
        "" t)
    in
    (r ^ ":" ^ (str_sisal_type ts))
   *)


(*let _ = 
let sis_rec = (
      Sisal_record [
        Field (
          Field_name "MASHI", 
          Sisal_array Real)])
in
let sis_uni1 = (
    Sisal_union [
      Tag ("MASHI", Real); 
      Tag ("MOSHI", sis_rec)])
in
let sis_uni2 = (
  Sisal_union [
    Tag ("NoMode", Null); 
    Tag ("ListElement",
          Sisal_record [
            Field (
              Field_name "Data",
              Integer);
            Field (
              Field_name "Next",
              Integer)])])
in
  print_endline (str_sisal_type (Sisal_array Real));
  print_endline (str_sisal_type (
      Sisal_array (Sisal_array Real)));
  print_endline (str_sisal_type sis_rec);
  print_endline (str_sisal_type (Sisal_stream (sis_uni2)));
  print_endline (str_sisal_type sis_uni1)
  *)
(*
type
  sisal_type = 
    Boolean
  | Character
  | Double_real
  | Integer
  | Null
  | Real
  | Compound_type of compound_type
  | Type_name of type_name
and
  compound_type =
    Sisal_array  of sisal_type
  | Sisal_stream of sisal_type
  | Sisal_record of (field list)
  | Sisal_union  of (tag list)
and
  field =
    Field of (field_name * sisal_type)
and
  tag =
    Tag of (tag_name * sisal_type)
and field_name =
  Field_name of string
| Field_names of (string list)
and tag_name = string
and type_name = string

type sisal_constant =
  | Constant of sisal_type
  | Error of sisal_type
type array_value = { t : sisal_type ; lo : int; hi : int }
type stream_value = { t : sisal_type ; hi : int }
   *)
