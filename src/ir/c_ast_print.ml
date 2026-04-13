open C_ast

let string_of_qualifier = function
  | Const -> "const"
  | Volatile -> "volatile"
  | Restrict -> "restrict"

let rec string_of_c_type = function
  | Basic s -> s
  | Pointer (ty, quals) ->
      let q_str = List.map string_of_qualifier quals |> String.concat " " in
      Printf.sprintf "%s *%s" (string_of_c_type ty) (if q_str = "" then "" else q_str ^ " ")
  | Array (ty, Some size) -> Printf.sprintf "%s[%d]" (string_of_c_type ty) size
  | Array (ty, None) -> Printf.sprintf "%s[]" (string_of_c_type ty)
  | Vector (ty, size) -> 
      Printf.sprintf "%s __attribute__((vector_size(%d)))" (string_of_c_type ty) size
  | Struct (name, fields) ->
      if fields = [] then "struct " ^ name
      else Printf.sprintf "struct %s { %s }" name (string_of_fields fields)
  | Union (name, fields) ->
      if fields = [] then "union " ^ name
      else Printf.sprintf "union %s { %s }" name (string_of_fields fields)
  | Void -> "void"

and string_of_fields fields =
  fields 
  |> List.map (fun (name, ty) -> Printf.sprintf "%s %s;" (string_of_c_type ty) name)
  |> String.concat " "

let string_of_binary_op = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Shl -> "<<" | Shr -> ">>"
  | BitAnd -> "&" | BitOr -> "|" | BitXor -> "^"
  | LogAnd -> "&&" | LogOr -> "||"
  | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | Assign -> "="
  | AssignAdd -> "+=" | AssignSub -> "-=" | AssignMul -> "*=" | AssignDiv -> "/="

let string_of_unary_op = function
  | PreInc -> "++" | PostInc -> "++"
  | PreDec -> "--" | PostDec -> "--"
  | AddrOf -> "&" | Deref -> "*"
  | Negate -> "-" | BitNot -> "~" | LogNot -> "!"

let rec string_of_expr = function
  | Id s -> s
  | LitInt i -> string_of_int i
  | LitFloat f -> 
      let s = string_of_float f in
      if String.contains s '.' then s ^ "f" else s ^ ".0f"
  | LitString s -> Printf.sprintf "\"%s\"" s
  | BinOp (op, e1, e2) ->
      Printf.sprintf "(%s %s %s)" (string_of_expr e1) (string_of_binary_op op) (string_of_expr e2)
  | UnaryOp (op, e) ->
      begin match op with
      | PostInc | PostDec -> Printf.sprintf "(%s%s)" (string_of_expr e) (string_of_unary_op op)
      | _ -> Printf.sprintf "(%s%s)" (string_of_unary_op op) (string_of_expr e)
      end
  | Call (name, args) ->
      Printf.sprintf "%s(%s)" name (String.concat ", " (List.map string_of_expr args))
  | Index (e1, e2) -> Printf.sprintf "%s[%s]" (string_of_expr e1) (string_of_expr e2)
  | Member (e, f) -> Printf.sprintf "%s.%s" (string_of_expr e) f
  | Arrow (e, f) -> Printf.sprintf "%s->%s" (string_of_expr e) f
  | Cast (ty, e) -> Printf.sprintf "((%s)%s)" (string_of_c_type ty) (string_of_expr e)
  | Cond (c, t, f) -> Printf.sprintf "(%s ? %s : %s)" (string_of_expr c) (string_of_expr t) (string_of_expr f)

let rec string_of_stmt indent = 
  let pad = String.make (indent * 2) ' ' in
  function
  | Decl (ty, name, Some init) ->
      Printf.sprintf "%s%s %s = %s;" pad (string_of_c_type ty) name (string_of_expr init)
  | Decl (ty, name, None) ->
      Printf.sprintf "%s%s %s;" pad (string_of_c_type ty) name
  | Expr e -> Printf.sprintf "%s%s;" pad (string_of_expr e)
  | For (init, cond, step, body) ->
      let init_s = String.trim (string_of_stmt 0 init) in
      let init_s = if String.length init_s > 0 && init_s.[String.length init_s - 1] = ';' 
                   then String.sub init_s 0 (String.length init_s - 1) 
                   else init_s in
      Printf.sprintf "%sfor (%s; %s; %s) {\n%s\n%s}" 
        pad init_s (string_of_expr cond) (string_of_expr step)
        (String.concat "\n" (List.map (string_of_stmt (indent + 1)) body))
        pad
  | While (cond, body) ->
      Printf.sprintf "%swhile (%s) {\n%s\n%s}" 
        pad (string_of_expr cond)
        (String.concat "\n" (List.map (string_of_stmt (indent + 1)) body))
        pad
  | DoWhile (body, cond) ->
      Printf.sprintf "%sdo {\n%s\n%s} while (%s);" 
        pad 
        (String.concat "\n" (List.map (string_of_stmt (indent + 1)) body))
        pad (string_of_expr cond)
  | If (cond, t, f) ->
      let then_s = String.concat "\n" (List.map (string_of_stmt (indent + 1)) t) in
      let else_s = if f = [] then "" else 
        Printf.sprintf "\n%selse {\n%s\n%s}" pad 
          (String.concat "\n" (List.map (string_of_stmt (indent + 1)) f)) pad
      in
      Printf.sprintf "%sif (%s) {\n%s\n%s}%s" pad (string_of_expr cond) then_s pad else_s
  | Return (Some e) -> Printf.sprintf "%sreturn %s;" pad (string_of_expr e)
  | Return None -> pad ^ "return;"
  | Break -> pad ^ "break;"
  | Continue -> pad ^ "continue;"
  | Pragma s -> Printf.sprintf "%s#pragma %s" pad s
  | GCDApply (count, queue, (idx, body)) ->
      Printf.sprintf "%sdispatch_apply(%s, %s, ^(size_t %s) {\n%s\n%s});" 
        pad (string_of_expr count) queue idx
        (String.concat "\n" (List.map (string_of_stmt (indent + 1)) body))
        pad
  | MetalKernel k ->
      let params_s = k.params 
        |> List.map (fun (ty, name, idx) -> 
            Printf.sprintf "device %s %s [[buffer(%d)]]" (string_of_c_type ty) name idx)
        |> String.concat ", "
      in
      Printf.sprintf "%skernel void %s(%s) {\n%s\n%s}"
        pad k.name params_s
        (String.concat "\n" (List.map (string_of_stmt (indent + 1)) k.body))
        pad
  | Compound stmts ->
      Printf.sprintf "%s{\n%s\n%s}" pad
        (String.concat "\n" (List.map (string_of_stmt (indent + 1)) stmts))
        pad
  | Comment s -> Printf.sprintf "%s// %s" pad s

let string_of_procedure p =
  let params_s = 
    p.params 
    |> List.map (fun (ty, name) -> Printf.sprintf "%s %s" (string_of_c_type ty) name)
    |> String.concat ", "
  in
  let prefix = if p.extern_c then "extern \"C\" " else "" in
  Printf.sprintf "%s%s %s(%s) {\n%s\n}"
    prefix (string_of_c_type p.return_ty) p.name params_s
    (String.concat "\n" (List.map (string_of_stmt 1) p.body))

let string_of_unit u =
  let inc_s = List.map (fun s -> "#include <" ^ s ^ ">") u.includes |> String.concat "\n" in
  let glob_s = List.map (string_of_stmt 0) u.globals |> String.concat "\n" in
  let proc_s = List.map string_of_procedure u.procedures |> String.concat "\n\n" in
  String.concat "\n\n" [inc_s; glob_s; proc_s]
