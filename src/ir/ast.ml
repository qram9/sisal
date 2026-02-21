type field = Field of field_name list
and field_name = Field_name of string
and field_exp = Field_exp of field * simple_exp
and field_def = Field_def of field_name * simple_exp
and sexpr_pair = SExpr_pair of simple_exp * exp
and type_def = Type_def of type_name * sisal_type
and tag_exp = Tag_name of tag_name | Tag_exp of tag_name * simple_exp

and iterator_terminator =
  | Iterator_termination of iterator * termination_test
  | Termination_iterator of termination_test * iterator

and iterator = Repeat of decldef_part
and termination_test = While of exp | Until of exp

and decl =
  | Decl_with_type of decl_id list * sisal_type
  | Decl_no_type of decl_id list

and decl_id = Decl_name of string | Decl_func of function_header

and simple_exp =
  (* Graphics Vector Constructor vec4(1.0, 2.0, 3.0, 1.0) *)
  | Vec of vec_type * exp list
  | Mat of mat_type * exp list
  | Constant of sisal_constant
  | Old of value_name
  | Val of value_name
  | Paren of exp
  | Invocation of function_name * arg
  | Array_ref of simple_exp * exp
  | Array_generator_named of type_name
  | Array_generator_unnamed of sexpr_pair
  | Array_generator_named_addr of type_name * sexpr_pair
  | Array_replace of simple_exp * sexpr_pair list
  | Stream_generator of type_name
  | Stream_generator_exp of type_name * exp
  | Stream_generator_unknown_exp of exp
  | Record_ref of simple_exp * field_name
  | Record_generator_named of type_name * field_def list
  | Record_generator_unnamed of field_def list
  | Record_generator_primary of simple_exp * field_exp list
  | Is of tag_name * exp
  | Union_generator of type_name * tag_exp
  | Is_error of exp
  | Prefix_operation of prefix_name * exp
  | If of cond list * last_else
  | Let_rec of decldef_part * exp
  | Let of decldef_part * exp
  | Tagcase of tagassign_exp * tagnames_colon_exp list * otherwise
  | For_all of in_exp * decldef_part * return_clause list
  | For_initial of decldef_part * iterator_terminator * return_clause list
  | Not of simple_exp
  | Negate of simple_exp
  | Pipe of simple_exp * simple_exp
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
  | Lambda of function_header * exp

and exp = Exp of simple_exp list | Empty
and cond = Cond of exp * exp
and last_else = Else of exp
and otherwise = Otherwise of exp

and tagassign_exp =
  | Assign of value_name * simple_exp
  | Tagcase_exp of simple_exp

and tagnames = Tagnames of string list
and tagnames_colon_exp = Tag_list of tagnames * exp
and arg = Arg of exp
and function_name = Function_name of string list

and function_header =
  | Function_header of function_name * decl list * sisal_type list
  | Function_header_nodec of function_name * sisal_type list

and function_def =
  | Forward_function of function_header
  | Function of function_leaf list

and function_leaf =
  | Function_single of
      (function_header * type_def list * function_leaf list * exp)

and define = Define of function_name list

(* Which is then used in our ordered fragments *)
and compilation_unit = Compilation_unit of top_fragment list
and fun_returns = Returns of sisal_type list
and decldef = Decldef of (decl list * exp)
and decldef_part = Decldef_part of decldef list
and reduction_op = Sum | Product | Least | Greatest | Catenate | No_red
and direction_op = Left | Right | Tree | No_dir

and in_exp =
  | In_exp of value_name * exp
  | At_exp of in_exp * value_names
  | Dot of in_exp * in_exp
  | Cross of in_exp * in_exp

and value_name = Value_name of string list
and value_names = Value_names of string list

and return_exp =
  | Value_of of direction_op * reduction_op * simple_exp
  | Array_of of simple_exp
  | Stream_of of simple_exp

and masking_clause = Unless of simple_exp | When of simple_exp | No_mask

and return_clause =
  | Return_exp of return_exp * masking_clause
  | Old_ret of return_exp * masking_clause

and sisal_constant =
  | Byte of int
  | Char of string
  | Double of float
  | Error of sisal_type
  | False
  | Float of float
  | Half of float
  | Int of int
  | Long of int64
  | Nil
  | Short of int
  | String of string
  | True
  | Ubyte of int
  | Uchar of int
  | Uint of int
  | Ulong of int64
  | Ushort of int

and prefix_name =
  | Boolean_prefix
  | Byte_prefix
  | Char_prefix
  | Double_prefix
  | Half_prefix
  | Integer_prefix
  | Long_prefix
  | Real_prefix
  | Short_prefix
  | Ubyte_prefix
  | Uchar_prefix
  | Uint_prefix
  | Ulong_prefix
  | Ushort_prefix

and sisal_type =
  | Boolean
  | Byte_ty
  | Character
  | Compound_type of compound_type
  | Double_real
  | Error_ty of string
  | Half_ty
  | Integer
  | Long_ty
  | Mat_ty of mat_type
  | Null
  | Real
  | Short_ty
  | Type_name of type_name
  | Ubyte_ty (* 8-bit  *)
  | Uchar_ty
  | Uint_ty (* 32-bit *)
  | Ulong_ty
  | Ushort_ty (* 16-bit *)
  | Vec_ty of vec_type

and vec_type =
  (* Basic vector types *)
  | Byte2
  | Byte3
  | Byte4
  | Byte8
  | Byte16
  | Char2
  | Char3
  | Char4
  | Char8
  | Char16
  | Double2
  | Double3
  | Double4
  | Double8
  | Double16
  | Float2
  | Float3
  | Float4
  | Float8
  | Float16
  | Half2
  | Half3
  | Half4
  | Half8
  | Half16
  | Int2
  | Int3
  | Int4
  | Int8
  | Int16
  | Long2
  | Long3
  | Long4
  | Long8
  | Long16
  | Short2
  | Short3
  | Short4
  | Short8
  | Short16
  | Ubyte2
  | Ubyte3
  | Ubyte4
  | Ubyte8
  | Ubyte16
  | Uchar2
  | Uchar3
  | Uchar4
  | Uchar8
  | Uchar16
  | Uint2
  | Uint3
  | Uint4
  | Uint8
  | Uint16
  | Ulong2
  | Ulong3
  | Ulong4
  | Ulong8
  | Ulong16
  | Ushort2
  | Ushort3
  | Ushort4
  | Ushort8
  | Ushort16

and mat_type =
  (* --- Matrices --- *)
  | Mat2
  | Mat3
  | Mat4

and compound_type =
  | Sisal_array of sisal_type
  | Sisal_stream of sisal_type
  | Sisal_record of (string list * sisal_type) list
  | Sisal_union of (string list * sisal_type) list
  | Sisal_function_type of (string * sisal_type list * sisal_type list)
  | Sisal_union_enum of string list

and tag_name = string
and type_name = string
and using = Using of (string * string option) list

and top_fragment =
  | F_Using of using
  | F_Define of define
  | F_Types of type_def list
  | F_Globals of function_header list
  | F_Functions of function_def list
  | F_Skip

(* Stringify *)

let space_cate a b cha =
  match b with "" -> a | _ -> ( match a with "" -> b | _ -> a ^ cha ^ b)

let myfold c = List.fold_left (fun last fs -> space_cate last fs c) ""

let mypad1 c d =
  let k = String.make c ' ' in
  match d with "" -> "" | _ -> k ^ d

let mypad c d = match d with "" -> "" | _ -> c ^ d
let semicolon_fold = myfold ";"

let semicolon_newline_fold ?offset =
  let o = match offset with None -> 0 | Some r -> r in
  let k = String.make o ' ' in
  List.fold_left (fun last fs -> space_cate last (mypad k fs) ";\n") ""

let comma_fold = myfold ","
let space_fold = myfold " "

let basic_type_list =
  [
    Boolean;
    Byte_ty;
    Character;
    Double_real;
    Half_ty;
    Integer;
    Long_ty;
    Real;
    Short_ty;
    Ubyte_ty;
    Uchar_ty;
    Uint_ty;
    Ulong_ty;
    Ushort_ty;
    Mat_ty Mat2;
    Mat_ty Mat3;
    Mat_ty Mat4;
    Vec_ty Byte2;
    Vec_ty Byte3;
    Vec_ty Byte4;
    Vec_ty Byte8;
    Vec_ty Byte16;
    Vec_ty Char2;
    Vec_ty Char3;
    Vec_ty Char4;
    Vec_ty Char8;
    Vec_ty Char16;
    Vec_ty Double2;
    Vec_ty Double3;
    Vec_ty Double4;
    Vec_ty Double8;
    Vec_ty Double16;
    Vec_ty Float2;
    Vec_ty Float3;
    Vec_ty Float4;
    Vec_ty Float8;
    Vec_ty Float16;
    Vec_ty Half2;
    Vec_ty Half3;
    Vec_ty Half4;
    Vec_ty Half8;
    Vec_ty Half16;
    Vec_ty Int2;
    Vec_ty Int3;
    Vec_ty Int4;
    Vec_ty Int8;
    Vec_ty Int16;
    Vec_ty Long2;
    Vec_ty Long3;
    Vec_ty Long4;
    Vec_ty Long8;
    Vec_ty Long16;
    Vec_ty Short2;
    Vec_ty Short3;
    Vec_ty Short4;
    Vec_ty Short8;
    Vec_ty Short16;
    Vec_ty Ubyte2;
    Vec_ty Ubyte3;
    Vec_ty Ubyte4;
    Vec_ty Ubyte8;
    Vec_ty Ubyte16;
    Vec_ty Uchar2;
    Vec_ty Uchar3;
    Vec_ty Uchar4;
    Vec_ty Uchar8;
    Vec_ty Uchar16;
    Vec_ty Uint2;
    Vec_ty Uint3;
    Vec_ty Uint4;
    Vec_ty Uint8;
    Vec_ty Uint16;
    Vec_ty Ulong2;
    Vec_ty Ulong3;
    Vec_ty Ulong4;
    Vec_ty Ulong8;
    Vec_ty Ulong16;
    Vec_ty Ushort2;
    Vec_ty Ushort3;
    Vec_ty Ushort4;
    Vec_ty Ushort8;
    Vec_ty Ushort16;
  ]
(* let map =
  List.fold_left
    (fun acc (k, v) -> StringMap.add k v acc)
    StringMap.empty
    [("a", 1); ("b", 2); ("c", 3)]*)

let basic_float_list =
  [
    Double_real;
    Half_ty;
    Mat_ty Mat2;
    Mat_ty Mat3;
    Mat_ty Mat4;
    Real;
    Vec_ty Double2;
    Vec_ty Double3;
    Vec_ty Double4;
    Vec_ty Double8;
    Vec_ty Double16;
    Vec_ty Float2;
    Vec_ty Float3;
    Vec_ty Float4;
    Vec_ty Float8;
    Vec_ty Float16;
    Vec_ty Half2;
    Vec_ty Half3;
    Vec_ty Half4;
    Vec_ty Half8;
    Vec_ty Half16;
  ]

let basic_type_code =
  [
    (Boolean, "B");
    (Byte_ty, "Y");
    (Character, "C");
    (Double_real, "D");
    (Half_ty, "H");
    (Integer, "I");
    (Long_ty, "L");
    (Mat_ty Mat2, "M2");
    (Mat_ty Mat3, "M3");
    (Mat_ty Mat4, "M4");
    (Real, "F");
    (Short_ty, "S");
    (Ubyte_ty, "UY");
    (Uchar_ty, "UC");
    (Uint_ty, "U");
    (Ulong_ty, "UL");
    (Ushort_ty, "US");
    (Vec_ty Byte2, "V2Y");
    (Vec_ty Byte3, "V3Y");
    (Vec_ty Byte4, "V4Y");
    (Vec_ty Byte8, "V8Y");
    (Vec_ty Byte16, "V16Y");
    (Vec_ty Char2, "V2C");
    (Vec_ty Char3, "V3C");
    (Vec_ty Char4, "V4C");
    (Vec_ty Char8, "V8C");
    (Vec_ty Char16, "V16C");
    (Vec_ty Double2, "V2D");
    (Vec_ty Double3, "V3D");
    (Vec_ty Double4, "V4D");
    (Vec_ty Double8, "V8D");
    (Vec_ty Double16, "V16D");
    (Vec_ty Float2, "V2F");
    (Vec_ty Float3, "V3F");
    (Vec_ty Float4, "V4F");
    (Vec_ty Float8, "V8F");
    (Vec_ty Float16, "V16F");
    (Vec_ty Half2, "V2H");
    (Vec_ty Half3, "V3H");
    (Vec_ty Half4, "V4H");
    (Vec_ty Half8, "V8H");
    (Vec_ty Half16, "V16H");
    (Vec_ty Int2, "V2I");
    (Vec_ty Int3, "V3I");
    (Vec_ty Int4, "V4I");
    (Vec_ty Int8, "V8I");
    (Vec_ty Int16, "V16I");
    (Vec_ty Long2, "V2L");
    (Vec_ty Long3, "V3L");
    (Vec_ty Long4, "V4L");
    (Vec_ty Long8, "V8L");
    (Vec_ty Long16, "V16L");
    (Vec_ty Short2, "V2S");
    (Vec_ty Short3, "V3S");
    (Vec_ty Short4, "V4S");
    (Vec_ty Short8, "V8S");
    (Vec_ty Short16, "V16S");
    (Vec_ty Ubyte2, "V2UY");
    (Vec_ty Ubyte3, "V3UY");
    (Vec_ty Ubyte4, "V4UY");
    (Vec_ty Ubyte8, "V8UY");
    (Vec_ty Ubyte16, "V16UY");
    (Vec_ty Uchar2, "V2UC");
    (Vec_ty Uchar3, "V3UC");
    (Vec_ty Uchar4, "V4UC");
    (Vec_ty Uchar8, "V8UC");
    (Vec_ty Uchar16, "V16UC");
    (Vec_ty Uint2, "V2UI");
    (Vec_ty Uint3, "V3UI");
    (Vec_ty Uint4, "V4UI");
    (Vec_ty Uint8, "V8UI");
    (Vec_ty Uint16, "V16UI");
    (Vec_ty Ulong2, "V2UL");
    (Vec_ty Ulong3, "V3UL");
    (Vec_ty Ulong4, "V4UL");
    (Vec_ty Ulong8, "V8UL");
    (Vec_ty Ulong16, "V16UL");
    (Vec_ty Ushort2, "V2US");
    (Vec_ty Ushort3, "V3US");
    (Vec_ty Ushort4, "V4US");
    (Vec_ty Ushort8, "V8US");
    (Vec_ty Ushort16, "V16US");
  ]

module T = struct
  type t = string

  let compare = Stdlib.compare
end

module TM = Map.Make (T)

let newline_fold ?offset =
  let o = match offset with None -> 0 | Some r -> r in
  let k = String.make o ' ' in
  List.fold_left (fun last fs -> space_cate last (mypad k fs) "\n") ""

let dot_fold = myfold "."
let paren exp = "(" ^ exp ^ ")"
let brack exp = "[" ^ exp ^ "]"
let elseif_fold = myfold "\nELSE IF "

let rec str_tagnames = function Tagnames tn -> comma_fold tn

and mangle_intrinsic name args returns =
  let sym_map =
    List.fold_left
      (fun acc (k, v) -> TM.add (str_sisal_type k) v acc)
      TM.empty basic_type_code
  in
  let get_code t =
    try TM.find (str_sisal_type t) sym_map
    with Not_found -> "U" (* Default to 'U' for Unknown/User types *)
  in
  let arg_str = String.concat "" (List.map get_code args) in
  let ret_str = String.concat "" (List.map get_code returns) in

  (* Using double-underscore separator for "crackability" *)
  Printf.sprintf "_S%s__%s__%s" name arg_str ret_str

and str_direction = function
  | No_dir -> ""
  | Left -> "LEFT"
  | Right -> "RIGHT"
  | Tree -> "TREE"

and str_reduction = function
  | Sum -> "SUM"
  | Product -> "PRODUCT"
  | Least -> "LEAST"
  | Greatest -> "GREATEST"
  | Catenate -> "CATENATE"
  | No_red -> ""

and str_return_exp = function
  | Value_of (d, r, e) ->
      space_fold
        [ "VALUE OF"; str_direction d; str_reduction r; str_simple_exp e ]
  | Array_of e -> "ARRAY OF " ^ str_simple_exp e
  | Stream_of e -> "STREAM OF " ^ str_simple_exp e

and str_masking_clause = function
  | Unless e -> "UNLESS " ^ str_simple_exp e
  | When e -> "WHEN " ^ str_simple_exp e
  | No_mask -> ""

and str_iterator ?(offset = 0) = function
  | Repeat dp ->
      mypad1 offset "REPEAT\n" ^ str_decldef_part ~offset:(offset + 2) dp

and str_termination = function
  | While e -> "WHILE " ^ str_exp e
  | Until e -> "UNTIL " ^ str_exp e

and str_return_clause = function
  | Old_ret (re, mc) ->
      space_fold [ "OLD"; str_return_exp re; str_masking_clause mc ]
  | Return_exp (re, mc) ->
      space_fold [ str_return_exp re; str_masking_clause mc ]

and str_taglist = function
  | Tag_list (tns, e) -> "TAG " ^ str_tagnames tns ^ ":" ^ str_exp e

and str_taglist_list tls = newline_fold (List.map str_taglist tls)

and str_tagcase_exp = function
  | Assign (vn, e) -> "TAGCASE " ^ str_val vn ^ ":=" ^ str_simple_exp e
  | Tagcase_exp exp -> "TAGCASE " ^ str_simple_exp exp

and str_otherwise = function Otherwise e -> "OTHERWISE " ^ str_exp e
and str_colon_spec = function sl, s -> comma_fold sl ^ ":" ^ str_sisal_type s

and str_compound_type = function
  | Sisal_array s -> "ARRAY [" ^ str_sisal_type s ^ "]"
  | Sisal_stream s -> "STREAM [" ^ str_sisal_type s ^ "]"
  | Sisal_union union_ty_v ->
      "UNION ["
      ^ semicolon_fold
          (List.fold_right
             (fun (x, y) z -> (comma_fold x ^ " : " ^ str_sisal_type y) :: z)
             union_ty_v [])
      ^ "]"
  (*(space_cate ("UNION [" ^ (comma_fold stl)) (str_sisal_type s) ":") ^ "]"*)
  | Sisal_union_enum stl -> "UNION [" ^ comma_fold stl ^ "]"
  | Sisal_record ff ->
      "RECORD [" ^ semicolon_fold (List.map str_colon_spec ff) ^ "]"
  | Sisal_function_type (fn_name, tyargs, tyres) ->
      fn_name ^ "("
      ^ comma_fold (List.map (fun x -> str_sisal_type x) tyargs)
      ^ " returns "
      ^ comma_fold (List.map (fun x -> str_sisal_type x) tyres)
      ^ ")"

and str_sisal_type = function
  | Boolean -> "BOOLEAN"
  | Character -> "CHARACTER"
  | Double_real -> "DOUBLE_REAL"
  | Integer -> "INTEGER"
  | Null -> "NULL"
  | Real -> "REAL"
  | Byte_ty -> "BYTE"
  | Half_ty -> "HALF"
  | Uint_ty -> "UINT"
  | Ushort_ty -> "USHORT"
  | Short_ty -> "SHORT"
  | Ubyte_ty -> "UBYTE"
  | Uchar_ty -> "UCHAR"
  | Ulong_ty -> "ULONG"
  | Long_ty -> "LONG"
  | Compound_type ct -> str_compound_type ct
  | Type_name ty -> ty
  | Vec_ty vec_t -> str_vec_type vec_t
  | Mat_ty mat_t -> str_mat_type mat_t
  | Error_ty ss -> "ERROR " ^ ss

and str_mat_type = function Mat2 -> "MAT2" | Mat3 -> "MAT3" | Mat4 -> "MAT4"

and str_vec_type = function
  | Byte2 -> "BYTE2"
  | Byte3 -> "BYTE3"
  | Byte4 -> "BYTE4"
  | Byte8 -> "BYTE8"
  | Byte16 -> "BYTE16"
  | Char2 -> "CHAR2"
  | Char3 -> "CHAR3"
  | Char4 -> "CHAR4"
  | Char8 -> "CHAR8"
  | Char16 -> "CHAR16"
  | Double2 -> "DOUBLE2"
  | Double3 -> "DOUBLE3"
  | Double4 -> "DOUBLE4"
  | Double8 -> "DOUBLE8"
  | Double16 -> "DOUBLE16"
  | Float2 -> "FLOAT2"
  | Float3 -> "FLOAT3"
  | Float4 -> "FLOAT4"
  | Float8 -> "FLOAT8"
  | Float16 -> "FLOAT16"
  | Half2 -> "HALF2"
  | Half3 -> "HALF3"
  | Half4 -> "HALF4"
  | Half8 -> "HALF8"
  | Half16 -> "HALF16"
  | Int2 -> "INT2"
  | Int3 -> "INT3"
  | Int4 -> "INT4"
  | Int8 -> "INT8"
  | Int16 -> "INT16"
  | Long2 -> "LONG2"
  | Long3 -> "LONG3"
  | Long4 -> "LONG4"
  | Long8 -> "LONG8"
  | Long16 -> "LONG16"
  | Short2 -> "SHORT2"
  | Short3 -> "SHORT3"
  | Short4 -> "SHORT4"
  | Short8 -> "SHORT8"
  | Short16 -> "SHORT16"
  | Ubyte2 -> "UBYTE2"
  | Ubyte3 -> "UBYTE3"
  | Ubyte4 -> "UBYTE4"
  | Ubyte8 -> "UBYTE8"
  | Ubyte16 -> "UBYTE16"
  | Uchar2 -> "UCHAR2"
  | Uchar3 -> "UCHAR3"
  | Uchar4 -> "UCHAR4"
  | Uchar8 -> "UCHAR8"
  | Uchar16 -> "UCHAR16"
  | Uint2 -> "UINT2"
  | Uint3 -> "UINT3"
  | Uint4 -> "UINT4"
  | Uint8 -> "UINT8"
  | Uint16 -> "UINT16"
  | Ulong2 -> "ULONG2"
  | Ulong3 -> "ULONG3"
  | Ulong4 -> "ULONG4"
  | Ulong8 -> "ULONG8"
  | Ulong16 -> "ULONG16"
  | Ushort2 -> "USHORT2"
  | Ushort3 -> "USHORT3"
  | Ushort4 -> "USHORT4"
  | Ushort8 -> "USHORT8"
  | Ushort16 -> "USHORT16"

and str_constant = function
  | Byte b -> "0b" ^ string_of_int b
  | Char st -> "\"" ^ st ^ "\""
  | Double d -> string_of_float d ^ "d"
  | Error st -> "ERROR [" ^ str_sisal_type st ^ "]"
  | False -> "FALSE"
  | Float f -> string_of_float f ^ "f"
  | Half h -> string_of_float h ^ "h"
  | Int i -> string_of_int i
  | Long s -> Int64.to_string s
  | Nil -> "NIL"
  | Short s -> string_of_int s
  | String st -> "\"" ^ st ^ "\""
  | True -> "TRUE"
  | Ubyte b -> "0ub" ^ string_of_int b
  | Uchar i -> string_of_int i
  | Uint i -> string_of_int i
  | Ulong s -> Int64.to_string s
  | Ushort s -> "0s" ^ string_of_int s

and str_val = function Value_name vl -> String.concat "." vl

and str_val_names = function
  | Value_names v ->
      List.fold_right
        (fun x z -> if x = "" then z else if z = "" then x else x ^ "," ^ z)
        v ""

and str_exp ?(offset = 0) = function
  | Exp e -> comma_fold (List.map (str_simple_exp ~offset) e)
  | Empty -> ""

and str_sexp_pair = function
  | SExpr_pair (e, f) -> str_simple_exp e ^ ":" ^ str_exp f

and str_field_name = function Field_name f -> f

and str_field_exp = function
  | Field_exp (f, e) -> str_field f ^ ":" ^ str_simple_exp e

and str_field = function Field fl -> dot_fold (List.map str_field_name fl)

and str_field_def = function
  | Field_def (fn, ex) -> str_field_name fn ^ ":" ^ str_simple_exp ex

and str_cond ?(offset = 0) = function
  | Cond (c, e) -> str_exp c ^ " THEN\n" ^ str_exp ~offset:(offset + 2) e

and str_in_exp = function
  | In_exp (vn, e) -> str_val vn ^ " IN " ^ str_exp e
  | At_exp (ie, vn) -> str_in_exp ie ^ " AT " ^ str_val_names vn
  | Dot (ie1, ie2) -> str_in_exp ie1 ^ " DOT " ^ str_in_exp ie2
  | Cross (ie1, ie2) -> str_in_exp ie2 ^ " CROSS " ^ str_in_exp ie1

and str_if ?(offset = 0) f = "IF " ^ elseif_fold (List.map (str_cond ~offset) f)

and str_else ?(offset = 0) = function
  | Else e -> "\n" ^ mypad1 offset "ELSE " ^ str_exp ~offset e

and str_tag_exp = function
  | Tag_name tn -> tn
  | Tag_exp (tn, sexp) -> tn ^ ":" ^ str_simple_exp sexp

and str_prefix_name = function
  | Boolean_prefix -> "BOOLEAN"
  | Byte_prefix -> "BYTE"
  | Char_prefix -> "CHAR"
  | Double_prefix -> "DOUBLE_REAL"
  | Half_prefix -> "HALF"
  | Integer_prefix -> "INTEGER"
  | Long_prefix -> "LONG"
  | Real_prefix -> "REAL"
  | Short_prefix -> "SHORT"
  | Ubyte_prefix -> "UBYTE"
  | Uchar_prefix -> "UCHAR"
  | Uint_prefix -> "UINT"
  | Ulong_prefix -> "ULONG"
  | Ushort_prefix -> "USHORT"

and str_decldef ?(offset = 0) = function
  | Decldef (deca, expn) ->
      let chars_with_colon_eq =
        mypad1 offset (comma_fold (List.map (str_decl ~offset) deca)) ^ " := "
      in
      chars_with_colon_eq ^ str_exp ~offset expn

and str_decldef_part ?(offset = 0) = function
  | Decldef_part f ->
      semicolon_newline_fold (List.map (str_decldef ~offset:(offset + 2)) f)

and str_decl_id ?(_offset = 0) = function
  | Decl_name nam -> nam
  | Decl_func func -> str_function_header func

and str_decl ?(offset = 0) = function
  | Decl_with_type (x, y) ->
      comma_fold (List.map (str_decl_id ~_offset:offset) x)
      ^ ":" ^ str_sisal_type y
  | Decl_no_type x -> comma_fold (List.map (str_decl_id ~_offset:offset) x)

and str_function_name = function Function_name lf -> String.concat "." lf
and str_arg = function Arg e -> str_exp e
and get_vec_len x = int_of_string (str_vec_len x)

and str_vec_len = function
  | Byte2 | Char2 | Half2 | Short2 | Int2 | Float2 | Double2 | Ubyte2 | Uchar2
  | Ushort2 | Uint2 | Ulong2 | Long2 ->
      "2"
  | Byte3 | Char3 | Half3 | Short3 | Int3 | Float3 | Double3 | Ubyte3 | Uchar3
  | Ushort3 | Uint3 | Ulong3 | Long3 ->
      "3"
  | Byte4 | Char4 | Half4 | Short4 | Int4 | Long4 | Ulong4 -> "4"
  | Float4 | Double4 | Ubyte4 | Uchar4 | Ushort4 | Uint4 -> "4"
  | Byte8 | Char8 | Half8 | Short8 | Int8 | Float8 | Double8 | Ubyte8 | Uchar8
  | Ulong8 | Long8 | Ushort8 | Uint8 ->
      "8"
  | Byte16 | Char16 | Half16 | Short16 | Int16 | Float16 | Double16 | Ubyte16
  | Ulong16 | Long16 | Uchar16 | Ushort16 | Uint16 ->
      "16"

and str_mat_len = function Mat2 -> "2" | Mat3 -> "3" | Mat4 -> "4"
and get_mat_dim = function Mat2 -> 2 | Mat3 -> 3 | Mat4 -> 4

and str_simple_exp ?(offset = 0) = function
  | Constant x -> str_constant x
  | Old v -> "OLD " ^ str_val v
  | Val v -> str_val v
  | Paren e -> "(" ^ str_exp e ^ ")"
  | Invocation (fn, arg) -> str_function_name fn ^ "(" ^ str_arg arg ^ ")"
  | Lambda (header, e) ->
      "LAMBDA " ^ str_function_header header ^ "\n"
      ^ mypad1 (offset + 2) (str_exp ~offset:(offset + 2) e)
      ^ "\n" ^ mypad1 offset "END LAMBDA"
  | Vec (vect, exp) ->
      "VEC" ^ str_vec_len vect ^ "(" ^ comma_fold (List.map str_exp exp) ^ ")"
  | Mat (mat_t, exp) ->
      "MAT" ^ str_mat_len mat_t ^ "(" ^ comma_fold (List.map str_exp exp) ^ ")"
  | Not e -> "~" ^ str_simple_exp e
  | Negate e -> "-" ^ str_simple_exp e
  | Pipe (a, b) -> str_simple_exp a ^ " || " ^ str_simple_exp b
  | And (a, b) -> str_simple_exp a ^ " & " ^ str_simple_exp b
  | Divide (a, b) -> str_simple_exp a ^ " / " ^ str_simple_exp b
  | Multiply (a, b) -> str_simple_exp a ^ " * " ^ str_simple_exp b
  | Subtract (a, b) -> str_simple_exp a ^ " - " ^ str_simple_exp b
  | Add (a, b) -> str_simple_exp a ^ " + " ^ str_simple_exp b
  | Or (a, b) -> str_simple_exp a ^ " | " ^ str_simple_exp b
  | Not_equal (a, b) -> str_simple_exp a ^ " ~= " ^ str_simple_exp b
  | Equal (a, b) -> str_simple_exp a ^ " = " ^ str_simple_exp b
  | Lesser_equal (a, b) -> str_simple_exp a ^ " <= " ^ str_simple_exp b
  | Lesser (a, b) -> str_simple_exp a ^ " < " ^ str_simple_exp b
  | Greater_equal (a, b) -> str_simple_exp a ^ " >= " ^ str_simple_exp b
  | Greater (a, b) -> str_simple_exp a ^ " > " ^ str_simple_exp b
  | Array_ref (se, e) -> str_simple_exp se ^ "[" ^ str_exp e ^ "]"
  | Array_generator_named tn -> "ARRAY " ^ tn ^ "[]"
  | Array_generator_named_addr (tn, ep) ->
      "ARRAY " ^ tn ^ " [" ^ str_sexp_pair ep ^ "]"
  | Array_generator_unnamed ep -> "ARRAY " ^ " [" ^ str_sexp_pair ep ^ "]"
  | Array_replace (p, epl) ->
      space_fold
        [
          str_simple_exp p;
          "[";
          semicolon_fold (List.map str_sexp_pair epl);
          "]";
        ]
  | Record_ref (e, fn) -> str_simple_exp e ^ "." ^ str_field_name fn
  | Record_generator_primary (e, fdle) ->
      space_fold
        [
          str_simple_exp e;
          "REPLACE [";
          semicolon_fold (List.map str_field_exp fdle);
          "]";
        ]
  | Record_generator_unnamed fdl ->
      space_fold
        [ "RECORD ["; semicolon_fold (List.map str_field_def fdl); "]" ]
  | Record_generator_named (tn, fdl) ->
      space_fold
        [ "RECORD ["; tn; semicolon_fold (List.map str_field_def fdl); "]" ]
  | Stream_generator tn -> "STREAM " ^ tn ^ "[]"
  | Stream_generator_exp (tn, e) -> "STREAM " ^ tn ^ "[" ^ str_exp e ^ "]"
  | Stream_generator_unknown_exp e -> "STREAM " ^ "[" ^ str_exp e ^ "]"
  | Is (tn, e) -> "IS " ^ tn ^ "(" ^ str_exp e ^ ")"
  | Union_generator (tn, te) ->
      space_fold [ "UNION"; tn; "["; str_tag_exp te; "]" ]
  | Prefix_operation (pn, e) -> str_prefix_name pn ^ "(" ^ str_exp e ^ ")"
  | Is_error e -> "IS ERROR (" ^ str_exp e ^ ")"
  | Let_rec (dp, e) ->
      "LET_REC\n"
      ^ str_decldef_part ~offset:(offset + 2) dp
      ^ " IN\n"
      ^ mypad1 offset (str_exp ~offset e)
      ^ "\n" ^ mypad1 offset "END LET"
  | Let (dp, e) ->
      "LET\n"
      ^ str_decldef_part ~offset:(offset + 2) dp
      ^ "\n"
      ^ mypad1 (offset + 2) "IN\n"
      ^ mypad1 offset (str_exp ~offset e)
      ^ "\n" ^ mypad1 offset "END LET"
  | Tagcase (ae, tc, o) ->
      newline_fold [ str_tagcase_exp ae; str_taglist_list tc; str_otherwise o ]
  | If (cl, el) ->
      str_if ~offset cl ^ str_else ~offset el ^ "\n" ^ mypad1 offset "END IF"
  | For_all (i, d, r) ->
      "FOR " ^ str_in_exp i ^ "\n"
      ^ newline_fold ~offset:(offset + 2)
          [ str_decldef_part ~offset:(offset + 4) d; "RETURNS" ]
      ^ "\n"
      ^ newline_fold ~offset:(offset + 4) (List.map str_return_clause r)
      ^ "\n"
      ^ newline_fold ~offset [ "END FOR" ]
  | For_initial (d, i, r) ->
      let loopAOrB i =
        match i with
        | Iterator_termination (ii, t) ->
            let k =
              newline_fold ~offset
                [
                  str_iterator ~offset:(offset + 2) ii;
                  str_termination t;
                  "RETURNS " ^ space_fold (List.map str_return_clause r);
                ]
            in
            let l = str_decldef_part ~offset:(offset + 2) d in
            let m = "FOR INITIAL" in
            m ^ newline_fold ~offset [ l; "\n"; k; mypad1 offset "END FOR" ]
        | Termination_iterator (t, ii) ->
            let k = "FOR INITIAL" in
            let l = str_decldef_part ~offset:(offset + 2) d in
            let m =
              newline_fold ~offset
                [
                  str_termination t;
                  str_iterator ~offset:(offset + 2) ii;
                  "RETURNS " ^ space_fold (List.map str_return_clause r);
                ]
            in
            k ^ newline_fold ~offset [ l; m; mypad1 offset "END FOR" ]
      in
      loopAOrB i

and str_type_list tl = comma_fold (List.map str_sisal_type tl)

and str_defines = function
  | Define dn -> "DEFINE " ^ comma_fold (List.map str_function_name dn)

and str_global f = "GLOBAL " ^ str_function_header f

and str_using = function
  | Using [] -> ""
  | Using ali ->
      "USING "
      ^ comma_fold
          (List.map
             (fun (x, y) -> match y with Some n -> x ^ " AS " ^ n | None -> x)
             ali)

and str_top_fragment = function
  | F_Using u -> str_using u
  | F_Define d -> str_defines d
  | F_Types t -> semicolon_newline_fold ~offset:0 (List.map str_type_def t)
  | F_Globals g -> newline_fold (List.map str_global g)
  | F_Functions f -> newline_fold (List.map (str_function_def 0) f)
  | F_Skip -> ""

and str_compilation_unit = function
  | Compilation_unit fragments ->
      newline_fold (List.map str_top_fragment fragments)

and str_type_def = function
  | Type_def (n, t) -> space_fold [ "TYPE"; n; "="; str_sisal_type t ]

and internals o f =
  match f with
  | [] -> ""
  | Function_single (header, tdefs, nest, e) :: tl ->
      let s = mypad1 o ("FUNCTION " ^ str_function_header header) in
      let t =
        newline_fold ~offset:0
          [
            semicolon_newline_fold ~offset:(o + 2) (List.map str_type_def tdefs);
            internals (o + 2) nest;
          ]
      in
      let q = mypad1 (o + 2) (str_exp ~offset:(o + 2) e) in
      let r = mypad1 o "END FUNCTION" in
      let p = newline_fold [ s; t; q; r; internals o tl ] in
      p

and str_function_def o k =
  match k with
  | Function f -> mypad1 o (internals o f)
  | Forward_function f -> mypad1 o ("FORWARD FUNCTION " ^ str_function_header f)

and str_function_header = function
  | Function_header_nodec (fun_name, tl) ->
      space_fold
        [ str_function_name fun_name; paren ("RETURNS " ^ str_type_list tl) ]
  | Function_header (fun_name, decls, tl) ->
      space_fold
        [
          str_function_name fun_name;
          paren
            (semicolon_fold (List.map str_decl decls)
            ^ " RETURNS " ^ str_type_list tl);
        ]
