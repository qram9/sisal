
let mysplcon a b cha =
match b with 
| "" -> a
| _ -> (match a with 
  | "" -> b
  | _ -> a ^ cha ^ b)

let rec 
  str_forall_loop fl = 
  match fl with
  | `For (`Inexp_list il, `Returns_list rl) ->
    "FOR " ^ il ^ " RETURNS " ^ rl
and str_primary = function
  `False -> "False"
  | `Nil -> "Nil"
  | `True -> "True"
  | `Int ii -> string_of_int ii
  | `Float ff -> string_of_float ff
  | `Char cc -> cc
  | `String st -> st
  | `Error ts -> str_sisal_type ts
and str_sisal_type st =
  match st with 
  | `Boolean -> "BOOLEAN"
  | `Character -> "CHARACTER"
  | `Double_real -> "DOUBLE_REAL"
  | `Integer -> "INTEGER"
  | `Null -> "NULL"
  | `Real -> "REAL"
  | `Type_name  t    -> t
  | `Sisal_array  sa ->
    ("ARRAY"   ^ "[ " ^ (str_sisal_type  sa) ^ " ]")
  | `Sisal_stream ss ->
    ("STREAM"  ^ "[ " ^ (str_sisal_type  ss) ^ " ]")
  | `Sisal_record sr ->
    ("RECORD"  ^ "[ " ^ (foldf sr) ^ " ]")
  | `Sisal_union  su ->
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
  | `Field (f,ts) ->
    match f with
    | `Field_name af ->  
    (af ^ ":" ^ (str_sisal_type ts))
    | `Field_names cdrf -> 
      (List.fold_left
        (fun last fs -> (mysplcon last fs ","))
        "" cdrf)
and
  str_tag = function
  | `Tag (t,ts) -> (t ^ ":" ^ (str_sisal_type ts))


(*let _ = 
let sis_rec = (
      `Sisal_record [
        `Field (
          `Field_name "MASHI", 
          `Sisal_array `Real)])
in
let sis_uni1 = (
    `Sisal_union [
      `Tag ("MASHI", `Real); 
      `Tag ("MOSHI", sis_rec)])
in
let sis_uni2 = (
  `Sisal_union [
    `Tag ("NoMode", `Null); 
    `Tag ("ListElement",
          `Sisal_record [
            `Field (
              `Field_name "Data",
              `Integer);
            `Field (
              `Field_name "Next",
              `Integer)])])
in
  print_endline (str_sisal_type (`Sisal_array `Real));
  print_endline (str_sisal_type (
      `Sisal_array (`Sisal_array `Real)));
  print_endline (str_sisal_type sis_rec);
  print_endline (str_sisal_type (`Sisal_stream (sis_uni2)));
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
