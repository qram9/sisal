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

let mysplcon a b cha =
match b with 
| "" -> a
| _ -> (match a with 
  | "" -> b
  | _ -> a ^ cha ^ b)

let rec str_sisal_type st =
  match st with 
  | Boolean -> "BOOLEAN"
  | Character -> "CHARACTER"
  | Double_real -> "DOUBLE_REAL"
  | Integer -> "INTEGER"
  | Null -> "NULL"
  | Real -> "REAL"
  | Type_name  t    -> t
  | Compound_type c -> (str_compound_type c)
and foldf sr = 
  (List.fold_left (fun last fs -> (mysplcon last (str_field fs) ";")) "" sr) 
and foldu su = 
  (List.fold_left (fun last fs -> (mysplcon last (str_tag fs) ";")) "" su) 
and
  str_compound_type =
  function
  | Sisal_array  sa -> ("ARRAY"   ^ "[ " ^ (str_sisal_type  sa) ^ " ]")
  | Sisal_stream ss -> ("STREAM"  ^ "[ " ^ (str_sisal_type  ss) ^ " ]")
  | Sisal_record sr -> ("RECORD"  ^ "[ " ^ (foldf sr) ^ " ]")
  | Sisal_union  su -> ("UNION"   ^ "[ " ^ (foldu su) ^ " ]")
and
  str_field = function
  | Field (f,ts) ->
    match f with
    | Field_name af ->  
    (af ^ ":" ^ (str_sisal_type ts))
    | Field_names cdrf -> 
      (List.fold_left (fun last fs -> (mysplcon last fs ",")) "" cdrf)
and
  str_tag = function
  | Tag (t,ts) -> (t ^ ":" ^ (str_sisal_type ts))



let _ = 
let sis_rec = (Compound_type (Sisal_record [Field (Field_name "MASHI", Compound_type(Sisal_array Real))]))
in
let sis_uni = (Compound_type (Sisal_union [Tag ("MASHI", Real); Tag ("MOSHI", sis_rec)]))
in
let sis_uni1 = (Compound_type (Sisal_union [Tag ("NoMode", Null);
                                            Tag ("ListElement",
                                                 Compound_type(Sisal_record
                                                                 [Field (Field_name "Data", Integer);
                                                                  Field (Field_name "Next", Integer)]))]))
in
  print_endline (str_sisal_type (Compound_type (Sisal_array Real)));
  print_endline (str_sisal_type (Compound_type (Sisal_array (Compound_type (Sisal_array Real)))));
  print_endline (str_sisal_type sis_rec);
  print_endline (str_sisal_type (Compound_type (Sisal_stream (sis_uni))));
  print_endline (str_sisal_type sis_uni1)
