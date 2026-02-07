type field = Field of field_name list
and field_name = Field_name of string
and
  field_exp = Field_exp of field * simple_exp
and
  field_def = Field_def of field_name * simple_exp
and sexpr_pair = SExpr_pair of simple_exp * exp
and type_def = Type_def of type_name * sisal_type
and tag_exp = | Tag_name of tag_name | Tag_exp of tag_name * simple_exp
and iterator_terminator =
  | Iterator_termination of iterator * termination_test
  | Termination_iterator of termination_test * iterator
and iterator = Repeat of decldef_part
and termination_test = While of exp | Until of exp
and decl = Decl_some of decl_id list * sisal_type
         | Decl_none of decl_id list
and decl_id = Decl_name of string | Decl_func of function_header
and simple_exp =
  Constant of sisal_constant
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
| If of (cond list) * last_else
| Let_rec of decldef_part * exp
| Let of decldef_part * exp
| Tagcase of
    tagassign_exp * tagnames_colon_exp list * otherwise
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
| Lambda of function_header * exp
and exp = Exp of simple_exp list | Empty
and cond = Cond of exp * exp
and last_else = Else of exp
and otherwise = Otherwise of exp
and tagassign_exp = Assign of value_name * simple_exp | Tagcase_exp of simple_exp
and tagnames = Tagnames of string list
and tagnames_colon_exp = Tag_list of tagnames * exp
and arg = Arg of exp
and function_name = Function_name of string list
and function_header =
  Function_header of function_name * decl list * sisal_type list
| Function_header_nodec of function_name * sisal_type list
and function_def = Forward_function of function_header
                 | Function of function_leaf list
and function_leaf = Function_single of (function_header * (type_def list) * (function_leaf list) * exp)
and using = Using of string list
and define = Define of function_name list
and compilation_unit = Compilation_unit of using * define * (type_def list) * (function_header list) * function_def list
and fun_returns = Returns of sisal_type list
and decldef = Decldef of (decl list * exp)
and decldef_part = Decldef_part of decldef list
and reduction_op = Sum | Product | Least | Greatest | Catenate | No_red
and direction_op = Left | Right | Tree | No_dir
and in_exp = In_exp of value_name * exp
           | At_exp of in_exp * value_names
           | Dot of in_exp * in_exp
           | Cross of in_exp * in_exp
and value_name = Value_name of string list
and value_names = Value_names of string list
and return_exp = Value_of of direction_op * reduction_op * simple_exp
               | Array_of of simple_exp | Stream_of of simple_exp
and masking_clause = Unless of simple_exp | When of simple_exp | No_mask
and return_clause =
  Return_exp of return_exp * masking_clause
| Old_ret of  return_exp * masking_clause
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
| Sisal_record of (string list * sisal_type) list
| Sisal_union  of (string list * sisal_type) list
| Sisal_function_type of (string * sisal_type list * sisal_type list)
| Sisal_union_enum  of (string list)
and tag_name = string
and type_name = string

(* Stringify *)

let space_cate a b cha =
  match b with
  | "" -> a
  | _ -> (match a with
          | "" -> b
          | _ -> a ^ cha ^ b)

let myfold c =
  List.fold_left (fun last fs -> (space_cate last fs c)) ""
let mypad1 c d =
  let k = String.make c ' ' in
  match d with
  | "" -> ""
  | _ -> k ^ d

let mypad c d =
  match d with "" -> ""
             | _ -> c ^ d

let semicolon_fold = myfold ";"
let semicolon_newline_fold ?offset =
  let o = match offset with None -> 0 | Some r -> r in
  let k = String.make o ' ' in
  List.fold_left (fun last fs -> (space_cate last (mypad k fs) ";\n")) ""
let comma_fold = myfold ","
let space_fold = myfold " "
let newline_fold ?offset =
  let o = match offset with None -> 0 | Some r -> r in
  let k = String.make o ' ' in
  List.fold_left (fun last fs -> (space_cate last (mypad k fs) "\n")) ""
let dot_fold = myfold "."
let paren exp = "(" ^ exp ^ ")"
let brack exp = "[" ^ exp ^ "]"
let elseif_fold = myfold "\nELSE IF "

let rec
    str_tagnames = function
  | Tagnames tn -> comma_fold tn
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
  | Value_of (d,r,e) ->
     space_fold ["VALUE OF"; str_direction d; str_reduction r;str_simple_exp e]
  | Array_of e -> "ARRAY OF " ^ (str_simple_exp e)
  | Stream_of e -> "STREAM OF " ^ (str_simple_exp e)

and str_masking_clause = function
  | Unless e -> "UNLESS " ^ (str_simple_exp e)
  | When e -> "WHEN " ^ (str_simple_exp e)
  | No_mask -> ""
and str_iterator ?(offset=0) = function
  | Repeat dp -> (mypad1 offset "REPEAT\n") ^ (str_decldef_part ~offset:(offset+2) dp)
and str_termination = function
  | While e -> "WHILE " ^ (str_exp e)
  | Until e -> "UNTIL " ^ (str_exp e)
and str_return_clause = function
  | Old_ret (re,mc) ->
     space_fold ["OLD"; str_return_exp re; str_masking_clause mc]
  | Return_exp (re,mc) ->
     space_fold [str_return_exp re; str_masking_clause mc]
and str_taglist = function
  |  Tag_list (tns,e) -> "TAG " ^ (str_tagnames tns) ^ ":" ^ (str_exp e)
and str_taglist_list tls = newline_fold (List.map str_taglist tls)
and str_tagcase_exp = function
  |Assign (vn, e) -> "TAGCASE " ^ (str_val vn) ^ ":=" ^ (str_simple_exp e)
  | Tagcase_exp (exp) -> "TAGCASE " ^ (str_simple_exp exp)
and str_otherwise = function
  | Otherwise e -> "OTHERWISE " ^ (str_exp e)
and str_colon_spec = function
  | (sl,s) -> (comma_fold sl) ^ ":" ^ (str_sisal_type s)
and str_compound_type = function
  | Sisal_array s -> "ARRAY [" ^ str_sisal_type s ^ "]"
  | Sisal_stream s -> "STREAM [" ^ str_sisal_type s ^ "]"
  | Sisal_union union_ty_v ->
     "UNION [" ^
       (semicolon_fold
          (List.fold_right
             (fun (x, y) z -> ((comma_fold x) ^ " : " ^ (str_sisal_type y)) :: z)
             union_ty_v [])) ^ "]"
  (*(space_cate ("UNION [" ^ (comma_fold stl)) (str_sisal_type s) ":") ^ "]"*)
  | Sisal_union_enum  (stl) -> "UNION [" ^ (comma_fold stl) ^ "]"
  | Sisal_record ff -> "RECORD [" ^ (semicolon_fold (List.map str_colon_spec ff)) ^ "]"
  | Sisal_function_type (fn_name,tyargs,tyres) ->
     fn_name ^ "(" ^ (comma_fold (List.map (fun x -> str_sisal_type x) tyargs))
     ^ " returns " ^  (comma_fold (List.map (fun x -> str_sisal_type x)
                                     tyres)) ^ ")"
and
  str_sisal_type = function
  | Boolean -> "BOOLEAN"
  | Character -> "CHARACTER"
  | Double_real -> "DOUBLE_REAL"
  | Integer -> "INTEGER"
  | Null -> "NULL"
  | Real -> "REAL"
  | Compound_type ct ->
     str_compound_type ct
  | Type_name ty -> ty
and
  str_constant = function
  | False -> "FALSE" | Nil -> "NIL" | True -> "TRUE" | Int i -> string_of_int i
  | Float f -> string_of_float f | Char st -> "\"" ^ st  ^ "\""
  | String st -> "\"" ^ st ^ "\""
  | Error st -> "ERROR [" ^ (str_sisal_type st) ^ "]"
and
  str_val = function | Value_name vl -> String.concat "." vl
and str_using = function
  | Using [] -> ""
  | Using files -> 
      "USING " ^ (comma_fold (List.map (fun s -> "\"" ^ s ^ "\"") files)) 
and
  str_val_names = function
  | Value_names v ->
     List.fold_right
       (fun x z ->
         (if x = "" then
            z
          else if z = "" then
            x
          else x ^"," ^ z))
       v ""
and
  str_exp ?(offset=0) =
  function
  | Exp e -> comma_fold (List.map (str_simple_exp ~offset:offset) e)
  | Empty -> ""
and  str_sexp_pair = function
  | SExpr_pair (e,f) -> (str_simple_exp e) ^ ":" ^ (str_exp f)
and str_field_name = function
  | Field_name f -> f
and str_field_exp = function
  | Field_exp (f,e) -> (str_field f) ^ ":" ^ (str_simple_exp e)
and str_field = function
  | Field fl -> dot_fold (List.map str_field_name fl)
and str_field_def = function
  | Field_def (fn,ex) -> (str_field_name fn) ^ ":" ^ (str_simple_exp ex)
and str_cond ?(offset=0) = function
  | Cond (c,e) -> (str_exp c) ^ " THEN\n" ^ (str_exp ~offset:(offset+2) e)
and str_in_exp = function
  | In_exp (vn,e) -> (str_val vn) ^ " IN " ^ (str_exp e)
  | At_exp (ie,vn) -> (str_in_exp ie) ^ " AT "
                      ^ (str_val_names vn)
  | Dot (ie1,ie2) -> (str_in_exp ie1) ^ " DOT " ^ (str_in_exp ie2)
  | Cross (ie1,ie2) -> (str_in_exp ie2) ^ " CROSS " ^ (str_in_exp ie1)
and str_if ?(offset=0) f =
  "IF " ^
    (elseif_fold (List.map (str_cond ~offset:(offset)) f))
and str_else ?(offset=0) = function
  | Else e ->
     "\n" ^ (mypad1 offset "ELSE ") ^ (str_exp ~offset:(offset) e)
and str_tag_exp = function
    Tag_name tn -> tn
  | Tag_exp (tn,sexp) -> tn ^ ":" ^ (str_simple_exp sexp)
and str_prefix_name = function
  | Char_prefix -> "CHARACTER"
  | Double_prefix -> "DOUBLE"
  | Integer_prefix -> "INTEGER"
  | Real_prefix -> "REAL"
and str_decldef ?(offset=0) = function
  | Decldef (deca, expn) ->
     (comma_fold
       (List.map (str_decl ~offset:(offset)) deca)) ^ " := " ^ (str_exp expn)
and str_decldef_part ?(offset=0) = function
  | Decldef_part f ->
     semicolon_fold (List.map (str_decldef ~offset:(offset)) f)
and str_decl_id ?(_offset=0) = function
  | Decl_name nam -> nam
  | Decl_func func -> str_function_header func
and str_decl ?(offset=0) = function
  | Decl_some (x,y) ->
     (comma_fold
        (List.map (str_decl_id ~_offset:(offset)) x))
     ^ ":" ^ (str_sisal_type y)
  | Decl_none x ->
     (comma_fold (List.map (str_decl_id ~_offset:(offset)) x))
and str_function_name = function
  | Function_name lf -> String.concat "." lf
and str_arg = function | Arg e -> str_exp e
and str_simple_exp ?(offset=0) =
  function
  | Constant x -> str_constant x
  | Old v -> "OLD " ^ (str_val v)
  | Val v -> str_val v
  | Paren e -> "(" ^ str_exp e ^ ")"
  | Invocation(fn,arg) ->
     (str_function_name fn) ^ "(" ^ (str_arg arg) ^ ")"
  | Lambda (header, e) ->
      "LAMBDA " ^ (str_function_header header) ^ "\n" ^
      (mypad1 (offset + 2) (str_exp ~offset:(offset + 2) e)) ^ "\n" ^
      (mypad1 offset "END LAMBDA")
  | Not e -> "~" ^ (str_simple_exp e)
  | Negate e -> "-" ^ (str_simple_exp e)
  | Pipe (a,b) -> (str_simple_exp a) ^ " || " ^ (str_simple_exp b)
  | And (a,b) -> (str_simple_exp a) ^ " & " ^ (str_simple_exp b)
  | Divide (a,b) -> (str_simple_exp a) ^ " / " ^ (str_simple_exp b)
  | Multiply (a,b) -> (str_simple_exp a) ^ " * " ^ (str_simple_exp b)
  | Subtract (a,b) -> (str_simple_exp a) ^ " - " ^ (str_simple_exp b)
  | Add (a,b) -> (str_simple_exp a) ^ " + " ^ (str_simple_exp b)
  | Or (a,b) -> (str_simple_exp a) ^ " | " ^ (str_simple_exp b)
  | Not_equal (a,b) -> (str_simple_exp a) ^ " ~= " ^ (str_simple_exp b)
  | Equal (a,b) -> (str_simple_exp a) ^ " = " ^ (str_simple_exp b)
  | Lesser_equal (a,b) -> (str_simple_exp a) ^ " <= " ^ (str_simple_exp b)
  | Lesser (a,b) -> (str_simple_exp a) ^ " < " ^ (str_simple_exp b)
  | Greater_equal (a,b) -> (str_simple_exp a) ^ " >= " ^ (str_simple_exp b)
  | Greater (a,b) -> (str_simple_exp a) ^ " > " ^ (str_simple_exp b)
  | Array_ref (se,e) -> (str_simple_exp se) ^ "[" ^ (str_exp e) ^ "]"
  | Array_generator_named tn -> "ARRAY " ^ tn ^ "[]"
  | Array_generator_named_addr (tn,ep) ->
     "ARRAY " ^ tn ^ " [" ^ (str_sexp_pair ep) ^ "]"
  | Array_generator_unnamed ep ->
     "ARRAY " ^ " [" ^ (str_sexp_pair ep) ^ "]"
  | Array_replace (p,epl) ->
     space_fold [str_simple_exp p; "["; semicolon_fold (List.map str_sexp_pair epl); "]"]
  | Record_ref (e,fn) ->
     (str_simple_exp e) ^ "." ^ (str_field_name fn)
  | Record_generator_primary (e,fdle) ->
     space_fold [str_simple_exp e;
                 "REPLACE [";
                 (semicolon_fold (List.map str_field_exp fdle)); "]"]
  | Record_generator_unnamed (fdl) ->
     space_fold ["RECORD ["; semicolon_fold (List.map str_field_def fdl); "]"]
  | Record_generator_named (tn,fdl) ->
     space_fold ["RECORD ["; tn;
                 semicolon_fold (List.map str_field_def fdl); "]"]
  | Stream_generator tn -> "STREAM " ^ tn ^ "[]"
  | Stream_generator_exp (tn,e) -> "STREAM " ^ tn
                                   ^ "[" ^ (str_exp e) ^ "]"
  | Stream_generator_unknown_exp e -> "STREAM " ^  "[" ^ (str_exp e) ^ "]"
  | Is (tn,e) ->
     "IS " ^ tn ^ "(" ^ (str_exp e) ^ ")"
  | Union_generator (tn,te) ->
     space_fold ["UNION"; tn; "["; str_tag_exp te; "]"]
  | Prefix_operation (pn,e) -> (str_prefix_name pn) ^ "(" ^ (str_exp e) ^ ")"
  | Is_error e -> "IS ERROR (" ^ (str_exp e) ^ ")"
  | Let_rec (dp,e) ->
     ("LET REC\n" ) ^
       (str_decldef_part ~offset:(offset+2) dp) ^ " IN\n" ^
         (mypad1 (offset) (str_exp ~offset:(offset) e)) ^ "\n" ^
           (mypad1 offset "END LET")
  | Let (dp,e) ->
     ("LET\n" ) ^
       (str_decldef_part ~offset:(offset+2) dp) ^ " IN\n" ^
         (mypad1 (offset) (str_exp ~offset:(offset) e)) ^ "\n" ^
           (mypad1 offset "END LET")
  | Tagcase (ae,tc,o) ->
     newline_fold [str_tagcase_exp ae; str_taglist_list tc; str_otherwise o]
  | If (cl, el) ->
     (str_if ~offset:(offset) cl) ^
       (str_else ~offset:offset el) ^ "\n" ^
         (mypad1 offset "END IF")
  | For_all (i,d,r) ->
     "FOR " ^ (str_in_exp i) ^ "\n" ^
       (newline_fold ~offset:(offset+2)
          [str_decldef_part ~offset:(offset+4) d;
           "RETURNS";] ) ^ "\n" ^
         (newline_fold ~offset:(offset+4) (List.map str_return_clause r)) ^ "\n" ^
           (newline_fold ~offset:(offset) ["END FOR"])
  | For_initial (d,i,r) ->
     let loopAOrB i = match i with
       | Iterator_termination (ii,t) ->
          let k = (newline_fold ~offset:(offset)
                     [str_iterator ~offset:(offset+2) ii;
                      str_termination t;
                      "RETURNS " ^
                        (space_fold (List.map str_return_clause r))])
          in
          let l = (str_decldef_part ~offset:(offset+2) d)
          in
          let m = "FOR INITIAL" in
          m ^ (newline_fold ~offset:(offset) [l; "\n"; k; (mypad1 offset "END FOR")])
       | Termination_iterator (t,ii) ->
          let k = "FOR INITIAL" in
          let l =
            (str_decldef_part ~offset:(offset+2) d) in
          let m =
            newline_fold ~offset:(offset)
              [str_termination t;
               str_iterator ~offset:(offset+2)ii;
               "RETURNS " ^ (space_fold (List.map str_return_clause r))] in
          k ^ (newline_fold ~offset:(offset) [l;m;(mypad1 offset "END FOR")])
     in loopAOrB i
and str_type_list tl  = (comma_fold (List.map str_sisal_type tl))
and str_defines = function
  | Define dn -> "DEFINE " ^ comma_fold (List.map str_function_name dn)
and str_global f = "GLOBAL " ^ (str_function_header f)
and str_compilation_unit = function
  | Compilation_unit (_, defines,type_defs,globals,fdefs) ->
     newline_fold
       [str_defines defines;
        semicolon_newline_fold ~offset:0 (List.map str_type_def type_defs);
        newline_fold (List.map str_global globals);
        newline_fold (List.map
                        (str_function_def 0) fdefs)]
and str_type_def = function
  | Type_def (n,t) ->
     space_fold ["TYPE";n;"="; str_sisal_type t]
and internals o f =
  match f with
  |  [] -> ""
  | (Function_single (header,tdefs,nest,e))::tl ->
     let s =
       (mypad1 o ("FUNCTION " ^ (str_function_header header))) in
     let t =
       (newline_fold ~offset:0
          [(semicolon_newline_fold ~offset:(o+2)
              (List.map str_type_def tdefs));
           (internals (o+2) nest);]) in
     let q = mypad1 (o+2) (str_exp ~offset:(o+2) e) in
     let r = mypad1 o ("END FUNCTION") in
     let p = newline_fold[s ; t ; q ; r ; (internals (o) tl)] in
     p
and str_function_def o k = match k with
  | Function f ->
     mypad1 o (internals o f)
  | Forward_function f ->
     mypad1 o ("FORWARD FUNCTION " ^ (str_function_header f))
and str_function_header = function
  | Function_header_nodec (fun_name,tl) ->
     space_fold
       [(str_function_name fun_name);
        paren ("RETURNS " ^  (str_type_list tl))]
  | Function_header (fun_name, decls, tl) ->
     space_fold
       [str_function_name fun_name;
        paren ((semicolon_fold (List.map str_decl decls))
               ^ " RETURNS "  ^ (str_type_list tl))]

