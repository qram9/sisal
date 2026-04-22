open Ir.If1
module C = Ir.C_ast

module PortMap = Map.Make (struct
  type t = int * int (* node_id, port_id *)

  let compare = compare
end)

type env = {
  tm : if1_ty TM.t;
  var_map : C.expr PortMap.t;
  preds : (int * int) PortMap.t;
}

let sanitize name =
  let s = String.map (fun c -> if c = ' ' then '_' else c) name in
  String.lowercase_ascii s

let c_type_of_if1_basic = function
  | BOOLEAN -> C.Basic "bool"
  | BYTE | UBYTE -> C.Basic "uint8_t"
  | CHARACTER | UCHAR -> C.Basic "char"
  | DOUBLE -> C.Basic "double"
  | REAL -> C.Basic "float"
  | INTEGRAL -> C.Basic "int32_t"
  | LONG | ULONG -> C.Basic "int64_t"
  | SHORT | USHORT -> C.Basic "int16_t"
  | UINT -> C.Basic "uint32_t"
  | _ -> C.Basic "int32_t"

let rec c_type_of_if1_ty _tm = function
  | Basic b -> c_type_of_if1_basic b
  | Array_dv _elem_id -> C.Basic "sisal_array_t"
  | Array_ty elem_id ->
      let elem_ty = try TM.find elem_id _tm with _ -> Unknown_ty in
      C.Pointer (c_type_of_if1_ty _tm elem_ty, [])
  | Record (id, _, _) -> C.Basic ("struct_rec_" ^ string_of_int id)
  | Union (id, _, _) -> C.Basic ("union_un_" ^ string_of_int id)
  | _ -> C.Basic "void*"

let rec get_expr env nid pid =
  match PortMap.find_opt (nid, pid) env.var_map with
  | Some e -> e
  | None -> (
      match PortMap.find_opt (nid, pid) env.preds with
      | Some (sn, sp) -> get_expr env sn sp
      | None -> C.Id (Printf.sprintf "v_%d_%d" nid pid))

let c_binop_of_sym = function
  | ADD -> Some C.Add
  | SUBTRACT -> Some C.Sub
  | TIMES -> Some C.Mul
  | FDIVIDE | IDIVIDE -> Some C.Div
  | EQUAL -> Some C.Eq
  | NOT_EQUAL -> Some C.Ne
  | LESSER -> Some C.Lt
  | LESSER_EQUAL -> Some C.Le
  | GREATER -> Some C.Gt
  | GREATER_EQUAL -> Some C.Ge
  | AND | BITAND -> Some C.BitAnd
  | OR | BITOR -> Some C.BitOr
  | _ -> None

let c_unaop_of_sym = function
  | NEGATE -> Some C.Negate
  | NOT -> Some C.LogNot
  | _ -> None

let topo_sort gr =
  let rec visit (visited, stack) nid =
    if IntSet.mem nid visited then (visited, stack)
    else
      let visited = IntSet.add nid visited in
      let predecessors =
        ES.fold
          (fun ((sn, _), (dn, _), _) acc -> if dn = nid then sn :: acc else acc)
          gr.eset []
      in
      let visited, stack = List.fold_left visit (visited, stack) predecessors in
      (visited, nid :: stack)
  in
  let nodes = NM.bindings gr.nmap |> List.map fst in
  let _, stack = List.fold_left visit (IntSet.empty, []) nodes in
  List.rev stack

let rec lower_graph env gr =
  let preds =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) m -> PortMap.add (dn, dp) (sn, sp) m)
      gr.eset PortMap.empty
  in
  let env = { env with preds } in
  let sorted_nids = topo_sort gr in
  List.fold_left
    (fun (acc_stmts, curr_env) nid ->
      match NM.find_opt nid gr.nmap with
      | Some node ->
          let new_stmts, next_env = lower_node curr_env gr nid node in
          (acc_stmts @ new_stmts, next_env)
      | None -> (acc_stmts, curr_env))
    ([], env) sorted_nids

and lower_node env _gr nid node =
  match node with
  | Simple (_, sym, _, _, _) -> begin
      match c_binop_of_sym sym with
      | Some op ->
          let e1 = get_expr env nid 0 in
          let e2 = get_expr env nid 1 in
          let v_name = Printf.sprintf "v_%d" nid in
          let stmt =
            C.Decl (C.Basic "int32_t", v_name, Some (C.BinOp (op, e1, e2)))
          in
          let env =
            {
              env with
              var_map = PortMap.add (nid, 0) (C.Id v_name) env.var_map;
            }
          in
          ([ stmt ], env)
      | None -> (
          match c_unaop_of_sym sym with
          | Some op ->
              let e = get_expr env nid 0 in
              let v_name = Printf.sprintf "v_%d" nid in
              let stmt =
                C.Decl (C.Basic "int32_t", v_name, Some (C.UnaryOp (op, e)))
              in
              let env =
                {
                  env with
                  var_map = PortMap.add (nid, 0) (C.Id v_name) env.var_map;
                }
              in
              ([ stmt ], env)
          | None -> ([], env))
    end
  | Literal (_, code, value, _) ->
      let v_name = Printf.sprintf "lit_%d" nid in
      let lit =
        try
          match code with
          | REAL | DOUBLE -> C.LitFloat (float_of_string value)
          | _ -> C.LitInt (int_of_string value)
        with _ -> C.LitInt 0
      in
      let stmt = C.Decl (c_type_of_if1_basic code, v_name, Some lit) in
      let env =
        { env with var_map = PortMap.add (nid, 0) (C.Id v_name) env.var_map }
      in
      ([ stmt ], env)
  | Boundary (ins, _, _, _) ->
      let var_map =
        List.fold_left
          (fun m (_, pid, name) ->
            PortMap.add (0, pid) (C.Id (sanitize name)) m)
          env.var_map ins
      in
      ([], { env with var_map })
  | _ -> ([], env)

let lower_procedure tm nid node =
  match node with
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name s -> Some s | _ -> None) pr
        |> Option.value ~default:(Printf.sprintf "func_%d" nid)
      in
      let params =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.map
              (fun (_, pid, name) ->
                let ty_id =
                  ES.fold
                    (fun ((sn, sp), (_dn, _dp), t) acc ->
                      if sn = 0 && sp = pid then Some t else acc)
                    sub_gr.eset None
                  |> Option.value ~default:0
                in
                let if1_ty = try TM.find ty_id tm with _ -> Unknown_ty in
                (c_type_of_if1_ty tm if1_ty, sanitize name))
              ins
        | _ -> []
      in
      let env = { tm; var_map = PortMap.empty; preds = PortMap.empty } in
      let body, env_after = lower_graph env sub_gr in
      let ret_exprs =
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = 0 then (dp, get_expr env_after sn sp) :: acc else acc)
          sub_gr.eset []
        |> List.sort (fun (p1, _) (p2, _) -> compare p1 p2)
      in
      let body =
        match ret_exprs with
        | (_, e) :: _ -> body @ [ C.Return (Some e) ]
        | [] -> body
      in
      let ret_ty_id =
        ES.fold
          (fun ((_sn, _sp), (dn, dp), t) acc ->
            if dn = 0 && dp = 0 then Some t else acc)
          sub_gr.eset None
        |> Option.value ~default:0
      in
      let ret_ty =
        try TM.find ret_ty_id tm |> c_type_of_if1_ty tm with _ -> C.Void
      in
      Some
        {
          C.return_ty = ret_ty;
          name = func_name;
          params;
          body;
          extern_c = true;
        }
  | _ -> None

let translate (gr : graph) : C.translation_unit =
  let _, tm, _ = gr.typemap in
  let procedures =
    NM.fold
      (fun id node acc ->
        match lower_procedure tm id node with Some p -> p :: acc | None -> acc)
      gr.nmap []
  in
  {
    filename = "out.cpp";
    includes =
      [
        "stdio.h";
        "stdint.h";
        "stdbool.h";
        "dispatch/dispatch.h";
        "Accelerate/Accelerate.h";
        "sisal_runtime.h";
      ];
    globals = [];
    procedures;
  }
