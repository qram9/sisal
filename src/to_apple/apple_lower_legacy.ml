open Ir.If1
module C = Ir.C_ast

type direction = [ `In | `Out ]

module FullPortMap = Map.Make (struct
  type t = int * int * int * direction (* gid, node_id, port_id, direction *)

  let compare = compare
end)

module PortSet = Set.Make (struct
  type t = int * int * int * direction

  let compare = compare
end)

let next_gr_id = ref 0

let gen_gr_id () =
  let id = !next_gr_id in
  next_gr_id := id + 1;
  id

type env = {
  tm : if1_ty TM.t;
  var_map : C.expr FullPortMap.t;
  preds : (int * int * int * direction) FullPortMap.t;
  curr_gid : int;
  curr_gr : graph;
  parent_env : env option;
  force_gpu : bool;
}

let contains_substr s sub =
  let len_s = String.length s in
  let len_sub = String.length sub in
  if len_sub = 0 then true
  else if len_sub > len_s then false
  else
    let rec check i =
      if i + len_sub > len_s then false
      else if String.sub s i len_sub = sub then true
      else check (i + 1)
    in
    check 0

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

let var_name g n p dir =
  let d_str = match dir with `In -> "i" | `Out -> "o" in
  Printf.sprintf "v_g%d_n%d_p%d_%s" g n p d_str

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
  | _ -> C.Basic "float"

let c_type_of_if1_ty tm = function
  | Basic b -> c_type_of_if1_basic b
  | Array_dv _ | Array_ty _ -> C.Basic "sisal_array_t"
  | Record (id, _, _) -> C.Basic ("struct struct_rec_" ^ string_of_int id)
  | Union (id, _, _) -> C.Basic ("union union_un_" ^ string_of_int id)
  | _ -> C.Basic "float"

let type_id_of_if1_ty tm ty =
  match ty with
  | Basic REAL -> 0
  | Basic DOUBLE -> 1
  | Basic INTEGRAL -> 2
  | Basic BOOLEAN -> 3
  | Array_dv _ | Array_ty _ -> 10
  | _ -> 0

let rec get_expr ?(visited = PortSet.empty) env g n p dir =
  if PortSet.mem (g, n, p, dir) visited then C.Id (var_name g n p dir)
  else
    let visited = PortSet.add (g, n, p, dir) visited in
    match FullPortMap.find_opt (g, n, p, dir) env.var_map with
    | Some e -> e
    | None -> (
        match FullPortMap.find_opt (g, n, p, dir) env.preds with
        | Some (sg, sn, sp, sd) -> get_expr ~visited env sg sn sp sd
        | None -> (
            match env.parent_env with
            | Some p_env -> get_expr ~visited p_env g n p dir
            | None -> C.Id (var_name g n p dir)))

let get_port_type env gr nid pid dir =
  let ty_id =
    ES.fold
      (fun ((sn, sp), (dn, dp), t) acc ->
        let match_src = sn = nid && sp = pid && dir = `Out in
        let match_dst = dn = nid && dp = pid && dir = `In in
        if (match_src || match_dst) && t <> 0 then Some t else acc)
      gr.eset None
    |> Option.value ~default:0
  in
  try
    let if1_ty = TM.find ty_id env.tm in
    c_type_of_if1_ty env.tm if1_ty
  with _ -> (
    match NM.find_opt nid gr.nmap with
    | Some (Boundary (ins, outs, _, _)) ->
        if nid = 0 && dir = `Out then
          let ty_id =
            List.find_map
              (fun (t, p, _) -> if p = pid then Some t else None)
              ins
            |> Option.value ~default:0
          in
          try c_type_of_if1_ty env.tm (TM.find ty_id env.tm)
          with _ -> C.Basic "float"
        else if nid = 0 && dir = `In then
          let ty_id =
            ES.fold
              (fun ((sn, sp), (dn, dp), t) acc ->
                if dn = 0 && dp = pid && t <> 0 then Some t else acc)
              gr.eset None
            |> Option.value ~default:0
          in
          try c_type_of_if1_ty env.tm (TM.find ty_id env.tm)
          with _ -> C.Basic "float"
        else C.Basic "float"
    | _ -> C.Basic "float")

let get_elem_type env gr nid =
  let ty_id =
    ES.fold
      (fun ((sn, sp), _, t) acc ->
        if sn = nid && sp = 0 && t <> 0 then Some t else acc)
      gr.eset None
    |> Option.value ~default:0
  in
  try
    match TM.find ty_id env.tm with
    | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm
    | _ -> Unknown_ty
  with _ -> Unknown_ty

let string_of_pragma = function
  | Name s | Ast_type s | Subscript s -> s
  | _ -> ""

let rec collect_record_fields tm label =
  match TM.find_opt label tm with
  | Some (Record (field_ty_id, next_label, name)) ->
      let s_name = String.trim name in
      if s_name = "" || s_name = "UNKNOWN" then
        collect_record_fields tm next_label
      else
        let field_ty_val = try TM.find field_ty_id tm with _ -> Unknown_ty in
        if field_ty_val = Unknown_ty then collect_record_fields tm next_label
        else
          let field_ty = c_type_of_if1_ty tm field_ty_val in
          (sanitize name, field_ty) :: collect_record_fields tm next_label
  | _ -> []

let find_subgraph gr name =
  NM.choose_opt
    (NM.filter
       (fun _ n ->
         match n with
         | Compound (_, _, _, pr, _, _) ->
             let s_name =
               List.fold_left (fun acc p -> acc ^ string_of_pragma p) "" pr
             in
             contains_substr
               (String.uppercase_ascii s_name)
               (String.uppercase_ascii name)
         | _ -> false)
       gr.nmap)
  |> Option.map (fun (id, n) ->
      match n with Compound (_, _, _, _, g, _) -> (id, g) | _ -> assert false)

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

let rec lower_graph env gr gid =
  let env_ref = ref { env with curr_gid = gid; curr_gr = gr } in
  let agreement_body = ref [] in

  (* 1. Populate Preds from Local Edges *)
  let preds =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) m ->
        FullPortMap.add (gid, dn, dp, `In) (gid, sn, sp, `Out) m)
      gr.eset !env_ref.preds
  in
  env_ref := { !env_ref with preds };

  (* 2. Map and Alias Boundary Inputs (Node 0 Out ports) *)
  begin match NM.find_opt 0 gr.nmap with
  | Some (Boundary (ins, _, _, _)) ->
      List.iter
        (fun (ty_id, pid, name) ->
          let ty = get_port_type !env_ref gr 0 pid `Out in
          let local_v = var_name gid 0 pid `Out in
          let src_expr =
            try get_expr !env_ref gid 0 pid `Out
            with _ -> C.Id (sanitize name)
          in

          if src_expr <> C.Id local_v then
            agreement_body :=
              C.Decl (ty, local_v, Some src_expr) :: !agreement_body;
          env_ref :=
            {
              !env_ref with
              var_map =
                FullPortMap.add (gid, 0, pid, `Out) (C.Id local_v)
                  !env_ref.var_map;
            })
        ins
  | _ -> ()
  end;

  (* Pre-declare Boundary Outputs (Node 0 In ports) 
     We use both the 'outs' list and actual incoming edges to be robust. *)
  let b_outs_from_metadata =
    match NM.find_opt 0 gr.nmap with
    | Some (Boundary (_, outs, _, _)) -> List.mapi (fun i _ -> i) outs
    | _ -> []
  in
  let b_outs_from_edges =
    ES.fold
      (fun (_, (dn, dp), _) acc -> if dn = 0 then IntSet.add dp acc else acc)
      gr.eset IntSet.empty
    |> IntSet.elements
  in
  let all_b_outs =
    List.sort_uniq compare (b_outs_from_metadata @ b_outs_from_edges)
  in

  List.iter
    (fun pid ->
      let ty = get_port_type !env_ref gr 0 pid `In in
      let local_res_v = var_name gid 0 pid `In in
      agreement_body := C.Decl (ty, local_res_v, None) :: !agreement_body;
      env_ref :=
        {
          !env_ref with
          var_map =
            FullPortMap.add (gid, 0, pid, `In) (C.Id local_res_v)
              !env_ref.var_map;
        })
    all_b_outs;

  (* 3. COMPUTATION BLOCK *)
  let computation_body =
    let inner_decls = ref [] in
    let seen_decls = Hashtbl.create 16 in
    NM.iter
      (fun nid node ->
        if nid <> 0 then
          let pids =
            match node with
            | Simple (_, _, _, pout, _) | Literal (_, _, _, pout) ->
                List.init (Array.length pout) (fun i -> i)
            | Compound (_, _, _, _, sub_gr, _) ->
                (* Find all outputs of the compound node by looking at edges to node 0 in its subgraph *)
                ES.fold
                  (fun (_, (dn, dp), _) acc ->
                    if dn = 0 then dp :: acc else acc)
                  sub_gr.eset []
            | _ -> [ 0 ]
          in
          List.iter
            (fun pid ->
              let v = var_name gid nid pid `Out in
              if not (Hashtbl.mem seen_decls v) then (
                Hashtbl.add seen_decls v ();
                let ty = get_port_type !env_ref gr nid pid `Out in
                inner_decls := C.Decl (ty, v, None) :: !inner_decls;
                env_ref :=
                  {
                    !env_ref with
                    var_map =
                      FullPortMap.add (gid, nid, pid, `Out) (C.Id v)
                        !env_ref.var_map;
                  }))
            (List.sort_uniq compare pids))
      gr.nmap;

    let topo_sorted = topo_sort gr in
    let stmts =
      List.fold_left
        (fun acc nid ->
          if nid = 0 then acc
          else
            match NM.find_opt nid gr.nmap with
            | Some node ->
                let node_preds =
                  ES.filter (fun (_, (dn, dp), _) -> dn = nid) gr.eset
                in
                ES.iter
                  (fun ((sn, sp), (_, dp), _) ->
                    let src_expr = get_expr !env_ref gid sn sp `Out in
                    env_ref :=
                      {
                        !env_ref with
                        var_map =
                          FullPortMap.add (gid, nid, dp, `In) src_expr
                            !env_ref.var_map;
                      })
                  node_preds;
                acc @ lower_node !env_ref gr nid node
            | None -> acc)
        [] topo_sorted
    in

    let propagation =
      ES.fold
        (fun ((sn, sp), (dn, dp), _) acc ->
          if dn = 0 then
            let src = get_expr !env_ref gid sn sp `Out in
            let dst = C.Id (var_name gid 0 dp `In) in
            C.Expr (C.BinOp (C.Assign, dst, src)) :: acc
          else acc)
        gr.eset []
    in
    List.rev !inner_decls @ stmts @ propagation
  in
  (List.rev !agreement_body @ [ C.Compound computation_body ], !env_ref)

and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, ty, pr, loop_gr, assoc) ->
      let sub_gid = gen_gr_id () in
      let var_map_child =
        ES.fold
          (fun ((sn, sp), (dn, dp), _) m ->
            if dn = cid then
              let expr = get_expr env gid sn sp `Out in
              FullPortMap.add (sub_gid, 0, dp, `Out) expr m
            else m)
          gr.eset env.var_map
      in
      let is_real_forall =
        sy = INTERNAL
        && List.exists (function Name n -> n = "FORALL" | _ -> false) pr
      in
      if is_real_forall then
        let body_info = find_subgraph loop_gr "BODY" in
        let gen_info = find_subgraph loop_gr "GENERATOR" in

        let _, env_after_loop_header =
          lower_graph
            { env with var_map = var_map_child; parent_env = Some env }
            loop_gr sub_gid
        in

        let count_v =
          match gen_info with
          | Some (gen_nid, gen_gr) -> begin
              match
                NM.choose_opt
                  (NM.filter
                     (fun _ n ->
                       match n with
                       | Simple (_, RANGEGEN, _, _, _) -> true
                       | _ -> false)
                     gen_gr.nmap)
              with
              | Some (rg_nid, _) ->
                  get_expr env_after_loop_header sub_gid rg_nid 0 `Out
              | None -> (
                  match
                    NM.choose_opt
                      (NM.filter
                         (fun _ n ->
                           match n with
                           | Simple (_, ASIZE, _, _, _) -> true
                           | _ -> false)
                         gen_gr.nmap)
                  with
                  | Some (size_nid, _) ->
                      get_expr env_after_loop_header sub_gid size_nid 0 `Out
                  | None -> C.Id "0")
            end
          | None -> (
              match
                NM.choose_opt
                  (NM.filter
                     (fun _ n ->
                       match n with
                       | Simple (_, ASIZE, _, _, _) -> true
                       | _ -> false)
                     loop_gr.nmap)
              with
              | Some (size_nid, _) ->
                  get_expr env_after_loop_header sub_gid size_nid 0 `Out
              | None -> C.Id "0")
        in

        let res_v = get_expr env gid nid 0 `Out in
        let elem_ty =
          match get_elem_type env gr nid with
          | Unknown_ty -> TM.find 8 env.tm
          | ty -> ty
        in
        let tid = type_id_of_if1_ty env.tm elem_ty in
        match body_info with
        | Some (body_id, body_gr) ->
            let body_gid = gen_gr_id () in
            let var_map_body = ref env_after_loop_header.var_map in

            (* Correct capture: Map node 0 Out ports of body to sources in loop_gr *)
            ES.iter
              (fun ((sn, sp), (dn, dp), _) ->
                if dn = body_id then
                  let expr =
                    get_expr env_after_loop_header sub_gid sn sp `Out
                  in
                  var_map_body :=
                    FullPortMap.add (body_gid, 0, dp, `Out) expr !var_map_body)
              loop_gr.eset;

            let index_var = Printf.sprintf "v_idx_g%d" body_gid in
            (* Map index variable to correct port if it's an index port *)
            begin match NM.find_opt 0 body_gr.nmap with
            | Some (Boundary (body_ins, _, _, _)) ->
                List.iter
                  (fun (_, pid, name) ->
                    let sn = sanitize name in
                    if sn = "i" || sn = "idx" || sn = "v_idx" then
                      var_map_body :=
                        FullPortMap.add (body_gid, 0, pid, `Out)
                          (C.Id index_var) !var_map_body)
                  body_ins
            | _ -> ()
            end;

            let body_stmts, env_after_body =
              lower_graph
                {
                  env_after_loop_header with
                  var_map = !var_map_body;
                  parent_env = Some env_after_loop_header;
                }
                body_gr body_gid
            in

            (* Find result from body subgraph (node 0 in-port 0) *)
            let body_res =
              ES.fold
                (fun ((sn, sp), (dn, dp), _) acc ->
                  if dn = 0 && dp = 0 then
                    Some (get_expr env_after_body body_gid sn sp `Out)
                  else acc)
                body_gr.eset None
              |> Option.value ~default:(C.Id "0.0f")
            in

            let cast_ty =
              match c_type_of_if1_ty env.tm elem_ty with
              | C.Basic s -> s
              | _ -> "float"
            in
            let cast_ptr =
              C.Cast (C.Pointer (C.Basic cast_ty, []), C.Member (res_v, "data"))
            in
            let update_stmt =
              C.Expr
                (C.BinOp (C.Assign, C.Index (cast_ptr, C.Id index_var), body_res))
            in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     res_v,
                     C.Call
                       ( "sisal_array_alloc_empty",
                         [
                           C.LitInt 1;
                           C.LitInt tid;
                           C.Cast (C.Basic "uint64_t", count_v);
                         ] ) ));
              C.GCDApply
                ( count_v,
                  "dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, \
                   0)",
                  (index_var, body_stmts @ [ update_stmt ]) );
            ]
        | None ->
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     res_v,
                     C.Call
                       ( "sisal_array_alloc_empty",
                         [
                           C.LitInt 1;
                           C.LitInt tid;
                           C.Cast (C.Basic "uint64_t", count_v);
                         ] ) ));
            ]
      else
        let sub_stmts, env_after_sub =
          lower_graph
            { env with var_map = var_map_child; parent_env = Some env }
            loop_gr sub_gid
        in
        [ C.Compound sub_stmts ]
  | Simple (_, sym, pin, pout, pr) -> begin
      match
        match sym with
        | ADD -> Some C.Add
        | SUBTRACT -> Some C.Sub
        | TIMES -> Some C.Mul
        | FDIVIDE | IDIVIDE -> Some C.Div
        | EQUAL -> Some C.Eq
        | LESSER -> Some C.Lt
        | LESSER_EQUAL -> Some C.Le
        | GREATER -> Some C.Gt
        | GREATER_EQUAL -> Some C.Ge
        | OR -> Some C.LogOr
        | AND -> Some C.LogAnd
        | _ -> None
      with
      | Some op ->
          let e1 = get_expr env gid nid 0 `In in
          let e2 = get_expr env gid nid 1 `In in
          let v_res = get_expr env gid nid 0 `Out in
          [ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (op, e1, e2))) ]
      | None ->
          if sym = TYPECAST then
            let e = get_expr env gid nid 0 `In in
            let v_res = get_expr env gid nid 0 `Out in
            let ty = get_port_type env gr nid 0 `Out in
            [ C.Expr (C.BinOp (C.Assign, v_res, C.Cast (ty, e))) ]
          else if sym = RANGEGEN then
            let e1 = get_expr env gid nid 0 `In in
            let e2 = get_expr env gid nid 1 `In in
            let v_res = get_expr env gid nid 0 `Out in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     v_res,
                     C.BinOp (C.Add, C.BinOp (C.Sub, e2, e1), C.LitInt 1) ));
            ]
          else if sym = DV_ELEMENT || sym = AELEMENT then
            let arr = get_expr env env.curr_gid nid 0 `In in
            let idx = get_expr env env.curr_gid nid 1 `In in
            let v_res = get_expr env gid nid 0 `Out in
            let elem_ty = get_elem_type env gr nid in
            let cast_ty =
              match c_type_of_if1_ty env.tm elem_ty with
              | C.Basic s -> s
              | _ -> "float"
            in
            let cast_ptr =
              C.Cast (C.Pointer (C.Basic cast_ty, []), C.Member (arr, "data"))
            in
            let idx_cast =
              C.Cast
                ( C.Basic "size_t",
                  C.BinOp (C.Sub, idx, C.Member (arr, "lower_bound")) )
            in
            [ C.Expr (C.BinOp (C.Assign, v_res, C.Index (cast_ptr, idx_cast))) ]
          else if sym = ASIZE || sym = DV_DIMENSION then
            let arr = get_expr env gid nid 0 `In in
            let v_res = get_expr env gid nid 0 `Out in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     v_res,
                     C.Cast (C.Basic "int32_t", C.Member (arr, "size")) ));
            ]
          else if sym = DV_CREATE then
            let lb = get_expr env gid nid 0 `In in
            let size = get_expr env gid nid 1 `In in
            let v_res = get_expr env gid nid 0 `Out in
            let tid =
              match get_elem_type env gr nid with
              | Basic REAL -> 0
              | Basic DOUBLE -> 1
              | Basic INTEGRAL -> 2
              | Basic BOOLEAN -> 3
              | _ -> 0
            in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     v_res,
                     C.Call
                       ( "sisal_array_create",
                         [ lb; C.LitInt tid; C.Cast (C.Basic "int32_t", size) ]
                       ) ));
            ]
          else if sym = SELECT then
            let cond = get_expr env gid nid 0 `In in
            let v_then = get_expr env gid nid 1 `In in
            let v_else = get_expr env gid nid 2 `In in
            let v_res = get_expr env gid nid 0 `Out in
            [
              C.Expr (C.BinOp (C.Assign, v_res, C.Cond (cond, v_then, v_else)));
            ]
          else if sym = ERROR_NODE then
            let e = get_expr env gid nid 0 `In in
            let v_res = get_expr env gid nid 0 `Out in
            [ C.Expr (C.BinOp (C.Assign, v_res, e)) ]
          else []
    end
  | Literal (_, code, value, pout) ->
      let v_res = get_expr env gid nid 0 `Out in
      let lit =
        try
          match code with
          | REAL | DOUBLE -> C.LitFloat (float_of_string value)
          | BOOLEAN -> C.Id (String.lowercase_ascii value)
          | _ -> C.LitInt (int_of_string value)
        with _ -> C.LitInt 0
      in
      [ C.Expr (C.BinOp (C.Assign, v_res, lit)) ]
  | _ -> []

let lower_procedure tm nid node =
  next_gr_id := 0;
  match node with
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name s -> Some s | _ -> None) pr
        |> Option.value ~default:(Printf.sprintf "func_%d" nid)
      in
      let is_gpu_func =
        contains_substr (String.uppercase_ascii func_name) "GPU"
      in
      let sub_gid = gen_gr_id () in
      let params =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            let sorted_ins =
              List.sort (fun (_, p1, _) (_, p2, _) -> compare p1 p2) ins
            in
            List.map
              (fun (ty_id, pid, name) ->
                let sn = sanitize name in
                let if1_ty = try TM.find ty_id tm with _ -> Unknown_ty in
                let c_ty = c_type_of_if1_ty tm if1_ty in
                (c_ty, sn))
              sorted_ins
        | _ -> []
      in
      let var_map =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.fold_left
              (fun m (ty_id, pid, name) ->
                FullPortMap.add (sub_gid, 0, pid, `Out) (C.Id (sanitize name)) m)
              FullPortMap.empty ins
        | _ -> FullPortMap.empty
      in
      let env =
        {
          tm;
          var_map;
          preds = FullPortMap.empty;
          curr_gid = sub_gid;
          curr_gr = sub_gr;
          parent_env = None;
          force_gpu = is_gpu_func;
        }
      in
      let body_stmts, env_after = lower_graph env sub_gr sub_gid in

      (* Determine return values from both metadata and edges *)
      let b_outs_from_metadata =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (_, outs, _, _)) -> List.mapi (fun i _ -> i) outs
        | _ -> []
      in
      let b_outs_from_edges =
        ES.fold
          (fun (_, (dn, dp), _) acc ->
            if dn = 0 then IntSet.add dp acc else acc)
          sub_gr.eset IntSet.empty
        |> IntSet.elements
      in
      let all_b_outs =
        List.sort_uniq compare (b_outs_from_metadata @ b_outs_from_edges)
      in

      let ret_exprs =
        List.map
          (fun pid -> (pid, C.Id (var_name sub_gid 0 pid `In)))
          all_b_outs
      in

      let ret_count = List.length ret_exprs in
      if ret_count > 1 then
        let struct_name = func_name ^ "_results" in
        let fields =
          List.map
            (fun (dp, _) ->
              let ty = get_port_type env_after sub_gr 0 dp `In in
              ("res_" ^ string_of_int dp, ty))
            ret_exprs
        in
        let res_var = "res_obj" in
        let assigns =
          List.map
            (fun (dp, e) ->
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     C.Member (C.Id res_var, "res_" ^ string_of_int dp),
                     e )))
            ret_exprs
        in
        let final_body =
          body_stmts
          @ [ C.Decl (C.Basic ("struct " ^ struct_name), res_var, None) ]
          @ assigns
          @ [ C.Return (Some (C.Id res_var)) ]
        in
        Some
          ( {
              C.return_ty = C.Basic ("struct " ^ struct_name);
              name = func_name;
              params;
              body = final_body;
              extern_c = true;
            },
            Some (struct_name, fields) )
      else if ret_count = 1 then
        let dp, e = List.hd ret_exprs in
        let ty = get_port_type env_after sub_gr 0 dp `In in
        Some
          ( {
              C.return_ty = ty;
              name = func_name;
              params;
              body = body_stmts @ [ C.Return (Some e) ];
              extern_c = true;
            },
            None )
      else
        Some
          ( {
              C.return_ty = C.Void;
              name = func_name;
              params;
              body = body_stmts;
              extern_c = true;
            },
            None )
  | _ -> None

let translate (gr : graph) : C.translation_unit =
  let _, tm, _ = gr.typemap in
  let results =
    NM.fold
      (fun id node acc ->
        match lower_procedure tm id node with Some r -> r :: acc | None -> acc)
      gr.nmap []
  in
  let procedures = List.map fst results in
  let result_struct_decls =
    List.filter_map snd results
    |> List.map (fun (name, fields) ->
        C.Decl (C.Struct (name, fields), "", None))
  in
  let seen_field_lists = ref [] in
  let record_structs =
    TM.fold
      (fun id ty acc ->
        match ty with
        | Record _ ->
            let fields = collect_record_fields tm id in
            if fields = [] || List.mem fields !seen_field_lists then acc
            else (
              seen_field_lists := fields :: !seen_field_lists;
              C.Decl
                (C.Struct ("struct_rec_" ^ string_of_int id, fields), "", None)
              :: acc)
        | _ -> acc)
      tm []
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
    globals = record_structs @ result_struct_decls;
    procedures;
  }
