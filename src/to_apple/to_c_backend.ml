open Ir.If1
module C = Ir.C_ast

module PortMap = Map.Make (struct
  type t = int * int * int (* gid, node_id, port_id *)

  let compare = compare
end)

type env = {
  tm : if1_ty TM.t;
  var_map : C.expr PortMap.t;
  preds : (int * int * int) PortMap.t; (* (gid, dn, dp) -> (sgid, sn, sp) *)
  curr_gid : int;
  parent_env : env option;
  parent_nid : int option;
}

let next_gid = ref 0

let gen_gid () =
  let id = !next_gid in
  next_gid := id + 1;
  id

let sanitize name =
  let s =
    if String.starts_with ~prefix:"OLD " name then
      String.sub name 4 (String.length name - 4)
    else if String.starts_with ~prefix:"OLD_" name then
      String.sub name 4 (String.length name - 4)
    else name
  in
  let s = String.map (fun c -> if c = ' ' then '_' else c) s in
  String.lowercase_ascii s

let var_name g n p = Printf.sprintf "v_g%d_n%d_p%d" g n p

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

let rec c_type_of_if1_ty tm = function
  | Basic b -> c_type_of_if1_basic b
  | Array_dv _elem_id -> C.Basic "sisal_array_t"
  | Array_ty elem_id ->
      let elem_ty = try TM.find elem_id tm with _ -> Unknown_ty in
      C.Pointer (c_type_of_if1_ty tm elem_ty, [])
  | Record (id, _, _) -> C.Basic ("struct_rec_" ^ string_of_int id)
  | Union (id, _, _) -> C.Basic ("union_un_" ^ string_of_int id)
  | Tuple_ty _ -> C.Basic "void*"
  | _ -> C.Basic "void*"

let rec get_expr env g n p =
  match PortMap.find_opt (g, n, p) env.var_map with
  | Some e -> e
  | None -> (
      match PortMap.find_opt (g, n, p) env.preds with
      | Some (sg, sn, sp) -> get_expr env sg sn sp
      | None -> (
          match env.parent_env with
          | Some p_env -> get_expr p_env g n p
          | None -> C.Id (var_name g n p)))

let get_port_type env gr nid pid dir =
  let ty_id =
    ES.fold
      (fun ((sn, sp), (dn, dp), t) acc ->
        let matched =
          match dir with
          | `Out -> sn = nid && sp = pid
          | `In -> dn = nid && dp = pid
        in
        if matched && t <> 0 then Some t else acc)
      gr.eset None
  in
  match ty_id with
  | Some tid -> (
      try TM.find tid env.tm |> c_type_of_if1_ty env.tm
      with _ -> C.Basic "int32_t")
  | None -> C.Basic "int32_t"

let get_elem_type tm gr nid =
  let ty_id =
    ES.fold
      (fun ((sn, sp), _, t) acc ->
        if sn = nid && sp = 0 && t <> 0 then Some t else acc)
      gr.eset None
    |> Option.value ~default:0
  in
  try
    match TM.find ty_id tm with
    | Array_dv et_id | Array_ty et_id -> TM.find et_id tm
    | _ -> Unknown_ty
  with _ -> Unknown_ty

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
  let nodes = NM.bindings gr.nmap |> List.map fst in
  let num_nodes = List.length nodes in
  let in_degree = Hashtbl.create num_nodes in
  let adj_list = Hashtbl.create num_nodes in

  List.iter
    (fun id ->
      Hashtbl.add in_degree id 0;
      Hashtbl.add adj_list id [])
    nodes;

  (* Construct DAG using the edge-set.
     If edge starts at 0, it's from the boundary-input node (ignore for in-degree). *)
  ES.iter
    (fun ((sn, _), (dn, _), _) ->
      if sn <> 0 then begin
        if Hashtbl.mem in_degree dn && Hashtbl.mem adj_list sn then begin
          let current = Hashtbl.find in_degree dn in
          Hashtbl.replace in_degree dn (current + 1);
          let succs = Hashtbl.find adj_list sn in
          Hashtbl.replace adj_list sn (dn :: succs)
        end
      end)
    gr.eset;

  let worklist = Queue.create () in
  List.iter
    (fun id -> if Hashtbl.find in_degree id = 0 then Queue.add id worklist)
    nodes;

  let rec loop acc =
    if Queue.is_empty worklist then List.rev acc
    else
      let n = Queue.take worklist in
      let successors = Hashtbl.find adj_list n in
      List.iter
        (fun dn ->
          let d = Hashtbl.find in_degree dn - 1 in
          Hashtbl.replace in_degree dn d;
          if d = 0 then Queue.add dn worklist)
        successors;
      loop (n :: acc)
  in
  let sorted = loop [] in
  if List.length sorted < num_nodes then begin
    (* Fallback for malformed graphs (e.g. unexpected cycles) *)
    let visited = Hashtbl.create num_nodes in
    List.iter (fun id -> Hashtbl.add visited id true) sorted;
    let missing = List.filter (fun id -> not (Hashtbl.mem visited id)) nodes in
    sorted @ missing
  end
  else sorted

let rec lower_subgraph env gr gid =
  (* The strategy: { { } }
     Outer block for boundary vars (inputs/outputs of node 0).
     Inner block for local node variables and computation. *)
  let boundary = NM.find 0 gr.nmap in
  let b_ins, b_outs =
    match boundary with Boundary (i, o, _, _) -> (i, o) | _ -> ([], [])
  in

  let env_ref = ref { env with curr_gid = gid } in

  (* 1. Boundary Input Declarations and Bindings (Outer Block) *)
  let b_in_decls =
    List.map
      (fun (ty_id, pid, name) ->
        let s_name = sanitize name in
        let ty =
          try TM.find ty_id env.tm |> c_type_of_if1_ty env.tm
          with _ -> C.Basic "void*"
        in
        let v_name = var_name gid 0 pid in
        (* Initial binding: boundary variable gets value from 'outside' *)
        let init =
          match env.parent_env, env.parent_nid with
          | Some p_env, Some pnid ->
              (* Nested compound: get input from parent node pnid *)
              Some (get_expr p_env p_env.curr_gid pnid pid)
          | _ ->
              (* Top level or procedure: use sanitized name *)
              Some (C.Id s_name)
        in
        env_ref :=
          {
            !env_ref with
            var_map = PortMap.add (gid, 0, pid) (C.Id v_name) !env_ref.var_map;
          };
        C.Decl (ty, v_name, init))
      b_ins
  in

  (* 2. Boundary Output Declarations (Outer Block) *)
  let b_out_decls =
    List.map
      (fun (ty_id, pid) ->
        let ty =
          try TM.find ty_id env.tm |> c_type_of_if1_ty env.tm
          with _ -> C.Basic "void*"
        in
        let v_name = var_name gid 0 pid in
        env_ref :=
          {
            !env_ref with
            var_map = PortMap.add (gid, 0, pid) (C.Id v_name) !env_ref.var_map;
          };
        C.Decl (ty, v_name, None))
      b_outs
  in

  (* 3. Inner Block: Local Node Declarations *)
  let inner_decls = ref [] in
  NM.iter
    (fun nid node ->
      if nid <> 0 then
        let pids =
          match node with
          | Simple (_, _, _, pout, _) | Literal (_, _, _, pout) ->
              List.init (Array.length pout) (fun i -> i)
          | Compound (_, _, _, _, sub_gr, _) ->
              (* Compound outputs are linked to its boundary node's inputs *)
              ES.fold
                (fun (_, (dn, dp), _) acc -> if dn = 0 then dp :: acc else acc)
                sub_gr.eset []
          | _ -> [ 0 ]
        in
        List.iter
          (fun pid ->
            let v = var_name gid nid pid in
            let ty = get_port_type !env_ref gr nid pid `Out in
            inner_decls := C.Decl (ty, v, None) :: !inner_decls;
            env_ref :=
              {
                !env_ref with
                var_map = PortMap.add (gid, nid, pid) (C.Id v) !env_ref.var_map;
              })
          pids)
    gr.nmap;

  (* 4. Computation Code *)
  let preds =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) m ->
        PortMap.add (gid, dn, dp) (gid, sn, sp) m)
      gr.eset !env_ref.preds
  in
  env_ref := { !env_ref with preds };

  let sorted_nids = topo_sort gr in
  let computation_stmts =
    List.fold_left
      (fun acc nid ->
        if nid = 0 then acc
        else
          match NM.find_opt nid gr.nmap with
          | Some node -> acc @ fst (lower_node !env_ref gr nid node)
          | None -> acc)
      [] sorted_nids
  in

  (* 5. Propagation to Boundary Outputs (Inner Block) *)
  let propagation =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = 0 then
          let src = get_expr !env_ref gid sn sp in
          let dst = get_expr !env_ref gid 0 dp in
          C.Expr (C.BinOp (C.Assign, dst, src)) :: acc
        else acc)
      gr.eset []
  in

  let inner_block =
    C.Compound (List.rev !inner_decls @ computation_stmts @ propagation)
  in
  (C.Compound (b_in_decls @ b_out_decls @ [ inner_block ]), !env_ref)

and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Simple (_, sym, _, _, _) -> begin
      match c_binop_of_sym sym with
      | Some op ->
          let e1 = get_expr env gid nid 0 in
          let e2 = get_expr env gid nid 1 in
          let v_res = get_expr env gid nid 0 in
          ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (op, e1, e2))) ], env)
      | None -> (
          match c_unaop_of_sym sym with
          | Some op ->
              let e = get_expr env gid nid 0 in
              let v_res = get_expr env gid nid 0 in
              ([ C.Expr (C.BinOp (C.Assign, v_res, C.UnaryOp (op, e))) ], env)
          | None ->
              if sym = DV_ELEMENT || sym = AELEMENT then
                let arr = get_expr env gid nid 0 in
                let idx = get_expr env gid nid 1 in
                let v_res = get_expr env gid nid 0 in
                let elem_ty = get_elem_type env.tm gr nid in
                let c_elem_ty = c_type_of_if1_ty env.tm elem_ty in
                let cast_ptr =
                  C.Cast (C.Pointer (c_elem_ty, []), C.Member (arr, "data"))
                in
                let idx_expr =
                  C.BinOp (C.Sub, idx, C.Member (arr, "lower_bound"))
                in
                ( [
                    C.Expr
                      (C.BinOp (C.Assign, v_res, C.Index (cast_ptr, idx_expr)));
                  ],
                  env )
              else if sym = ASIZE || sym = DV_DIMENSION then
                let arr = get_expr env gid nid 0 in
                let v_res = get_expr env gid nid 0 in
                ( [ C.Expr (C.BinOp (C.Assign, v_res, C.Member (arr, "size"))) ],
                  env )
              else if sym = DV_CREATE then
                let lb = get_expr env gid nid 0 in
                let size = get_expr env gid nid 1 in
                let v_res = get_expr env gid nid 0 in
                (* Simplified DV_CREATE for 1D *)
                let tid =
                  match get_elem_type env.tm gr nid with
                  | Basic REAL -> 0
                  | Basic DOUBLE -> 1
                  | Basic INTEGRAL -> 2
                  | Basic BOOLEAN -> 3
                  | _ -> 0
                in
                ( [
                    C.Expr
                      (C.BinOp
                         ( C.Assign,
                           v_res,
                           C.Call
                             ( "sisal_array_create",
                               [
                                 lb;
                                 C.LitInt tid;
                                 C.Cast (C.Basic "int32_t", size);
                               ] ) ));
                  ],
                  env )
              else if sym = SELECT then
                let cond = get_expr env gid nid 0 in
                let v_then = get_expr env gid nid 1 in
                let v_else = get_expr env gid nid 2 in
                let v_res = get_expr env gid nid 0 in
                ( [
                    C.Expr
                      (C.BinOp (C.Assign, v_res, C.Cond (cond, v_then, v_else)));
                  ],
                  env )
              else ([], env))
    end
  | Literal (_, code, value, _) ->
      let v_res = get_expr env gid nid 0 in
      let lit =
        try
          match code with
          | REAL | DOUBLE -> C.LitFloat (float_of_string value)
          | BOOLEAN -> C.Id (String.lowercase_ascii value)
          | _ -> C.LitInt (int_of_string value)
        with _ -> C.LitInt 0
      in
      ([ C.Expr (C.BinOp (C.Assign, v_res, lit)) ], env)
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      (* For INTERNAL compound nodes (like procedures or named subgraphs), we lower the subgraph *)
      let sub_gid = gen_gid () in
      let sub_block, env_after =
        lower_subgraph
          { env with parent_env = Some env; parent_nid = Some nid }
          sub_gr sub_gid
      in
      (* Assign results back to this node's outputs using indirection through boundary vars *)
      let assignments =
        ES.fold
          (fun (_, (dn, dp), _) acc ->
            if dn = 0 then
              let src = get_expr env_after sub_gid 0 dp in
              let dst = get_expr env gid nid dp in
              C.Expr (C.BinOp (C.Assign, dst, src)) :: acc
            else acc)
          sub_gr.eset []
      in
      ([ C.Compound [ sub_block; C.Compound assignments ] ], env_after)
  | _ ->
      let sym_str =
        match node with
        | Simple (_, sym, _, _, _) -> Printf.sprintf "Simple(%s)" (Ir.If1.string_of_node_sym sym)
        | Compound (_, sym, _, _, _, _) -> Printf.sprintf "Compound(%s)" (Ir.If1.string_of_node_sym sym)
        | Literal (_, _, val_str, _) -> Printf.sprintf "Literal(%s)" val_str
        | Boundary _ -> "Boundary"
        | Unknown_node -> "Unknown_node"
      in
      failwith (Printf.sprintf "lower_node: node type not implemented: %s (nid=%d)" sym_str nid)

let lower_procedure tm nid node =
  match node with
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name s -> Some s | _ -> None) pr
        |> Option.value ~default:(Printf.sprintf "func_%d" nid)
      in
      let sub_gid = gen_gid () in
      let params =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.map
              (fun (ty_id, pid, name) ->
                let ty =
                  try TM.find ty_id tm |> c_type_of_if1_ty tm
                  with _ -> C.Basic "void*"
                in
                (ty, sanitize name))
              ins
        | _ -> []
      in

      let env =
        {
          tm;
          var_map = PortMap.empty;
          preds = PortMap.empty;
          curr_gid = sub_gid;
          parent_env = None;
          parent_nid = None;
        }
      in
      let body_stmt, env_after = lower_subgraph env sub_gr sub_gid in

      let ret_exprs =
        ES.fold
          (fun (_, (dn, dp), _) acc ->
            if dn = 0 then (dp, get_expr env_after sub_gid 0 dp) :: acc
            else acc)
          sub_gr.eset []
        |> List.sort (fun (p1, _) (p2, _) -> compare p1 p2)
      in

      let body = [ body_stmt ] in
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
  next_gid := 0;
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
