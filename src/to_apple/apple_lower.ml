(** apple_lower.ml: The "Apple Lowering" pass for Sisal. This module implements
    the complex logic of translating dataflow IF1 graphs into imperative C-AST
    nodes, optimized for Apple Silicon. *)

open Ir.If1
open Apple_env
open Apple_helpers

(** [c_op_of_node_sym sym] maps a basic IF1 node symbol to a C binary operator. *)
let c_op_of_node_sym = function
  | ADD -> Some C.Add | SUBTRACT -> Some C.Sub | TIMES -> Some C.Mul
  | EQUAL -> Some C.Eq | NOT_EQUAL -> Some C.Ne
  | GREATER -> Some C.Gt | GREATER_EQUAL -> Some C.Ge
  | LESSER -> Some C.Lt | LESSER_EQUAL -> Some C.Le | _ -> None

let string_of_c_type = function
  | C.Basic s -> s
  | C.Pointer (C.Basic s, _) -> s ^ "*"
  | _ -> "int32_t"

(* Return Some op_name when the FORALL's RETURNS subgraph folds to a scalar via REDUCE.
   Used by both infer_types (to suppress the sisal_array_t seed) and lower_forall. *)
let forall_fold_op loop_gr =
  (* A pure fold FORALL has exactly ONE body output (the element to reduce).
     Multi-output FORALLs (e.g. DV_CONFORM with array + boolean outputs) use the
     gather path instead, so return None for them. *)
  let body_out_count = match find_subgraph loop_gr "BODY" with
    | None -> 0
    | Some (_, b_gr) ->
        ES.fold (fun (_, (dn, _), _) acc -> if dn = 0 then acc + 1 else acc) b_gr.eset 0 in
  if body_out_count <> 1 then None
  else
  match find_subgraph loop_gr "RETURNS" with
  | None -> None
  | Some (_, ret_gr) ->
      NM.fold (fun reduce_nid node acc ->
        match node with
        | Simple (_, REDUCE, _, _, _) ->
            let op = ES.fold (fun ((sn, _), (dn, dp), _) a ->
              if dn = reduce_nid && dp = 0 then
                match NM.find_opt sn ret_gr.nmap with
                | Some (Literal (_, CHARACTER, value, _)) -> Some (String.lowercase_ascii value)
                | _ -> a
              else a
            ) ret_gr.eset None in
            (match op with Some _ -> op | None -> acc)
        | _ -> acc
      ) ret_gr.nmap None

(** [infer_types env gr gid] populates the type_table for the current graph hierarchy. *)
let infer_types env gr gid =
  let _, tm, _ = gr.typemap in
  let table = Hashtbl.create 256 in
  FullPortMap.iter (fun k v -> Hashtbl.replace table k v) env.type_table;

  let set_ty g n p d ty =
    let key = (g, n, p, d) in
    match Hashtbl.find_opt table key with
    | Some existing when existing = C.Basic "sisal_array_t" -> ()
    | _ -> Hashtbl.replace table key ty in

  (* Like set_ty but returns true when the value actually changed — used to drive pass2 fixpoint. *)
  let set_ty_c g n p d ty =
    let key = (g, n, p, d) in
    match Hashtbl.find_opt table key with
    | Some ex when ex = C.Basic "sisal_array_t" -> false
    | Some ex when ex = ty -> false
    | _ -> Hashtbl.replace table key ty; true in

  let get_ty g n p d = match Hashtbl.find_opt table (g, n, p, d) with Some ty -> ty | None -> C.Basic "float" in

  let rec pass1 g cur_gid =
    let cs, _ps = g.symtab in
    SM.iter (fun _ v ->
      let ty_val = try TM.find v.val_ty tm with _ -> Basic REAL in
      set_ty cur_gid v.val_def v.def_port `Out (c_type_of_if1_ty tm ty_val)
    ) cs;
    NM.iter (fun nid node ->
      match node with
      | Boundary _ -> ()
      | Literal (_, code, _, _) ->
          let ty = match code with | REAL | DOUBLE -> C.Basic "double" | BOOLEAN -> C.Basic "bool" | _ -> C.Basic "int32_t" in
          set_ty cur_gid nid 0 `Out ty
      | Simple (_, sym, _, outs, _) ->
          let is_int = List.mem sym [RANGEGEN; ALIML; ALIMH; ASIZE; DV_SCATTER; DV_DIMENSION; DV_NUM_RANK; DV_OFFSET_AT] in
          let is_arr = List.mem sym [DV_CREATE; DV_RESHAPE; DV_SLICE; DV_PERMUTE; DV_ROTATE; DV_COMPRESS; DV_OUTERPRODUCT; DV_SORT; DV_REVERSE; DV_RESHAPE_BY_SHAPE; DV_GATHER; AGATHER; ASCATTER; ABUILD; AFILL; ACREATE; RELEMENTS; AREPLACE] in
          let ty = if is_int then C.Basic "int32_t" else if is_arr then C.Basic "sisal_array_t" else C.Basic "float" in
          Array.iteri (fun i _ -> set_ty cur_gid nid i `Out ty) outs;
          if is_arr || List.mem sym [ALIML; ALIMH; ASIZE; DV_SCATTER; AELEMENT; DV_ELEMENT; DV_LOAD_LINEAR; DV_DIMENSION; DV_COMPRESS; DV_SORT; DV_REVERSE; DV_ROTATE; DV_SLICE; DV_PERMUTE; REDUCE_ALL] then
            set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
      | Compound (_, sym, _, pr, sub, _) ->
          let sub_gid = try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1 in
          let is_forall = get_compound_type pr = If1_forall in
          let is_fold = is_forall && forall_fold_op sub <> None in
          if (is_forall || sym = STREAM || sym = MAT) && not is_fold then
            set_ty cur_gid nid 0 `Out (C.Basic "sisal_array_t");
          pass1 sub sub_gid
      | _ -> ()
    ) g.nmap in

  let rec pass2 g cur_gid =
    let tm2 = get_typemap_tm g in
    let changed_edges = ES.fold (fun ((sn, sp), (dn, dp), ty_id) ch ->
      let sty = get_ty cur_gid sn sp `Out in
      let dty = get_ty cur_gid dn dp `In in
      (* Seed concrete types from edge type tags (e.g. INTEGRAL on DV_ELEMENT output edges) *)
      let c0 = match TM.find_opt ty_id tm2 with
        | Some edge_if1_ty ->
            let ety = c_type_of_if1_ty tm2 edge_if1_ty in
            if ety <> C.Basic "float" then
              (let c1 = if sty = C.Basic "float" then set_ty_c cur_gid sn sp `Out ety else false in
               let c2 = if dty = C.Basic "float" then set_ty_c cur_gid dn dp `In ety else false in
               c1 || c2)
            else false
        | None -> false in
      let sty = get_ty cur_gid sn sp `Out in
      let dty = get_ty cur_gid dn dp `In in
      let c1 = if sty <> C.Basic "float" && dty = C.Basic "float" then set_ty_c cur_gid dn dp `In sty else false in
      let c2 = if dty <> C.Basic "float" && sty = C.Basic "float" then set_ty_c cur_gid sn sp `Out dty else false in
      ch || c0 || c1 || c2
    ) g.eset false in
    let changed_nodes = NM.fold (fun nid node ch ->
      match node with
      | Simple (_, sym, _, _, _) ->
          let c1 =
            if List.mem sym [ALIML; ALIMH; ASIZE; AELEMENT; DV_ELEMENT; DV_LOAD_LINEAR; DV_DIMENSION; DV_COMPRESS; DV_SORT; DV_REVERSE; DV_ROTATE; DV_SLICE; DV_PERMUTE; REDUCE_ALL; AREPLACE]
            then let in0 = get_ty cur_gid nid 0 `In in
                 if in0 = C.Basic "float" then set_ty_c cur_gid nid 0 `In (C.Basic "sisal_array_t") else false
            else false in
          let c2 =
            if sym = AELEMENT || sym = DV_ELEMENT || sym = DV_LOAD_LINEAR || sym = DV_OFFSET_AT || sym = DV_DIMENSION || sym = AREPLACE
            then let in1 = get_ty cur_gid nid 1 `In in
                 if in1 = C.Basic "float" then set_ty_c cur_gid nid 1 `In (C.Basic "int32_t") else false
            else false in
          ch || c1 || c2
      | Compound (_, _, _, _, sub, _) ->
          let sub_gid = try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1 in
          let b_ins = match NM.find_opt 0 sub.nmap with Some (Boundary (ins, _, _, _)) -> List.length ins | _ -> 0 in
          (* Use eset to find actual boundary outputs — boundary outs metadata is often stale.
             Exclude error edges so error-flow ports aren't treated as return values. *)
          let sub_return_ports = ES.fold (fun (_, (dn, dp), ty) acc -> if dn = 0 && not (is_error_port ty sub) then IntSet.add dp acc else acc) sub.eset IntSet.empty in
          let c1 = List.fold_left (fun ch i ->
            let p_ty = get_ty cur_gid nid i `In in
            let c_ty = get_ty sub_gid 0 i `Out in
            let ca = if p_ty <> C.Basic "float" && c_ty = C.Basic "float" then set_ty_c sub_gid 0 i `Out p_ty else false in
            let cb = if c_ty <> C.Basic "float" && p_ty = C.Basic "float" then set_ty_c cur_gid nid i `In c_ty else false in
            ch || ca || cb
          ) false (List.init b_ins Fun.id) in
          let c2 = IntSet.fold (fun i ch ->
            let c_ty = get_ty sub_gid 0 i `In in
            let p_ty = get_ty cur_gid nid i `Out in
            let ca = if c_ty <> C.Basic "float" && p_ty = C.Basic "float" then set_ty_c cur_gid nid i `Out c_ty else false in
            let cb = if p_ty <> C.Basic "float" && c_ty = C.Basic "float" then set_ty_c sub_gid 0 i `In p_ty else false in
            ch || ca || cb
          ) sub_return_ports false in
          pass2 sub sub_gid;
          ch || c1 || c2
      | _ -> ch
    ) g.nmap false in
    if changed_edges || changed_nodes then pass2 g cur_gid in

  let rec pass0 g cur_gid =
    NM.iter (fun nid node ->
      match node with
      | Simple (_, sym, _, outs, _) ->
          let is_arr = List.mem sym [DV_CREATE; DV_RESHAPE; DV_SLICE; DV_PERMUTE; DV_ROTATE; DV_COMPRESS; DV_OUTERPRODUCT; DV_SORT; DV_REVERSE; DV_RESHAPE_BY_SHAPE; DV_GATHER; AGATHER; ASCATTER; ABUILD; AFILL; ACREATE; RELEMENTS; AREPLACE] in
          if is_arr then (
            Array.iteri (fun i _ -> set_ty cur_gid nid i `Out (C.Basic "sisal_array_t")) outs;
            set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
          );
          if List.mem sym [ALIML; ALIMH; ASIZE; DV_SCATTER; AELEMENT; DV_ELEMENT; DV_LOAD_LINEAR; DV_DIMENSION; DV_COMPRESS; DV_SORT; DV_REVERSE; DV_ROTATE; DV_SLICE; DV_PERMUTE; REDUCE_ALL] then
            set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
      | Compound (_, sym, _, pr, sub, _) ->
          let sub_gid = try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1 in
          let is_forall = get_compound_type pr = If1_forall in
          let is_fold = is_forall && forall_fold_op sub <> None in
          if (is_forall || sym = STREAM || sym = MAT) && not is_fold then
            set_ty cur_gid nid 0 `Out (C.Basic "sisal_array_t");
          pass0 sub sub_gid
      | _ -> ()
    ) g.nmap in

  pass0 gr gid;
  pass1 gr gid;
  pass2 gr gid;
  { env with type_table = Hashtbl.fold (fun k v m -> FullPortMap.add k v m) table FullPortMap.empty }

let get_final_ty env gid nid pid dir =
  match FullPortMap.find_opt (gid, nid, pid, dir) env.type_table with
  | Some ty -> ty
  | None -> C.Basic "float"

(** [is_proc_expr env g n] checks if a node represents a global procedure. *)
let is_proc_expr env g n =
  if g = 0 then
    match IntMap.find_opt n env.proc_map with
    | Some _ -> true
    | None -> false
  else false

(** [scan_fanout gr gid env] populates the fanout_map for the current graph. *)
let scan_fanout gr gid env =
  let fanout_map = ES.fold (fun ((sn, sp), _, _) fmap ->
    let key = (gid, sn, sp) in
    PortFanout.add key (1 + (match PortFanout.find_opt key fmap with Some c -> c | None -> 0)) fmap
  ) gr.eset env.fanout_map in
  { env with fanout_map }

(** [assign_with_cast env gid nid pid dir src_expr] emits an assignment with
    an optional declaration if the variable is seen for the first time. *)
let assign_with_cast env gid nid pid dir src_expr =
  let is_proc = match src_expr with 
    | C.Id n -> (String.length n >= 5 && String.sub n 0 5 = "func_") 
    | _ -> false in
  if is_proc || is_proc_expr env gid nid then
    ([ C.Comment ("Skipped function-as-value assignment: " ^ (match src_expr with C.Id n -> n | _ -> "unknown")) ], env)
  else
    let dst_ty = get_final_ty env gid nid pid dir in
    let g = get_graph_by_gid env gid in
    let name = get_c_name env.proc_map env.gid_name_map gid nid pid dir g in
    let v_res = C.Id name in
    let cast_expr = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type dst_ty); src_expr ]) in
    if StringSet.mem name env.seen_decls then
      ([ C.Expr (C.BinOp (C.Assign, v_res, cast_expr)) ], env)
    else
      let init_val = if dst_ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
      let decl = C.Decl (dst_ty, name, init_val) in
      let assign = C.Expr (C.BinOp (C.Assign, v_res, cast_expr)) in
      let env' = { env with seen_decls = StringSet.add name env.seen_decls; var_map = FullPortMap.add (gid, nid, pid, dir) v_res env.var_map } in
      ([ decl; assign ], env')

(** [declare_outputs env gr gid nid node] selectively pre-declares outputs
    of a compound node in its parent scope. *)
let declare_outputs env gr gid nid node =
  let out_pids, out_dir = match node with
    | Simple (_, _, _, outs, _) -> (Array.mapi (fun i _ -> i) outs |> Array.to_list, `Out)
    | Compound _ ->
        (* Derive from parent eset: all edges where this compound node is the source.
           This matches exactly the set lower_node's res_prop will iterate, ensuring
           every assigned port is pre-declared in the outer scope. *)
        let ports = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
        (ports, `Out)
    | _ -> ([], `Out) in
  List.fold_left (fun (acc_stmts, e) pid ->
    let name = get_c_name e.proc_map e.gid_name_map gid nid pid out_dir gr in
    if StringSet.mem name e.seen_decls then (acc_stmts, e)
    else
      let ty = get_final_ty e gid nid pid out_dir in
      let init_val = if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
      (acc_stmts @ [ C.Decl (ty, name, init_val) ],
       { e with seen_decls = StringSet.add name e.seen_decls;
                var_map = FullPortMap.add (gid, nid, pid, out_dir) (C.Id name) e.var_map })
  ) ([], env) out_pids

(** [pre_declare_graph_locals env gr gid] declares all symbols in the graph's
    LOCAL symtab and its outputs (Boundary inputs). *)
let pre_declare_graph_locals env gr gid =
  (* 1. Declare all named symbols from the LOCAL-SYM table, one C variable per name *)
  let cs, _ps = gr.symtab in
  let stmts1, env1 = SM.fold (fun _ v (acc_stmts, e) ->
    if is_proc_expr e gid v.val_def then (acc_stmts, e)
    else
      let name = Printf.sprintf "v_%s_n__%d_%s"
        (scope_of e.gid_name_map gid) v.val_def (sanitize v.val_name) in
      if StringSet.mem name e.seen_decls then (acc_stmts, e)
      else
        let ty = get_final_ty e gid v.val_def v.def_port `Out in
        let init_val = if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
        (acc_stmts @ [ C.Decl (ty, name, init_val) ],
         { e with seen_decls = StringSet.add name e.seen_decls;
                  var_map = FullPortMap.add (gid, v.val_def, v.def_port, `Out) (C.Id name) e.var_map })
  ) cs ([], env) in

  (* 2. Declare boundary in-ports (node 0 out-ports) by scanning the edge set.
        Boundary.ins adjacency list is unreliable (stale/debug only); edges are authoritative. *)
  let boundary_in_ports = ES.fold (fun ((sn, sp), _, _) acc ->
    if sn = 0 then IntSet.add sp acc else acc) gr.eset IntSet.empty in
  let stmts2, env2 = IntSet.fold (fun i (acc_stmts, e) ->
    let name = get_c_name e.proc_map e.gid_name_map gid 0 i `Out gr in
    if StringSet.mem name e.seen_decls then (acc_stmts, e)
    else
      let ty = get_final_ty e gid 0 i `Out in
      let init_val =
        match FullPortMap.find_opt (gid, 0, i, `Out) e.proc_param_map with
        | Some arg_expr -> Some arg_expr
        | None -> if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
      (acc_stmts @ [ C.Decl (ty, name, init_val) ],
       { e with seen_decls = StringSet.add name e.seen_decls;
                var_map = FullPortMap.add (gid, 0, i, `Out) (C.Id name) e.var_map })
  ) boundary_in_ports ([], env1) in
  (stmts1 @ stmts2, env2)
let init_boundary_ports env parent_gr compound_nid gr gid =
  if gid = 0 then ([], env)
  else
    (* Use parent_gr.eset edges into compound_nid — authoritative, never stale.
       Boundary.ins adjacency list is unreliable (stale/debug only). *)
    let pgid = match env.parent_env with Some pe -> pe.curr_gid | None -> (match IntMap.find_opt gid env.parent_map with Some (p, _) -> p | _ -> 0) in
    let edges_to_compound = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
      if dn = compound_nid then IntMap.add dp (sn, sp) acc else acc) parent_gr.eset IntMap.empty in
    IntMap.fold (fun dp (psrcN, psrcP) (acc_stmts, e) ->
      let src_opt =
        if psrcN = 0 then Some (get_expr e pgid psrcN psrcP `Out)
        else
          match FullPortMap.find_opt (pgid, psrcN, psrcP, `Out) e.var_map with
          | Some v -> Some v
          | None ->
              (* Multi-level reference: source not found in immediate parent scope.
                 Walk up ancestor envs (e.g. REDUCE_ALL in proc scope referenced
                 from inside a FORALL body inside a LET body). *)
              let rec search env_up =
                match env_up.parent_env with
                | None -> None
                | Some pe ->
                    match FullPortMap.find_opt (pe.curr_gid, psrcN, psrcP, `Out) e.var_map with
                    | Some v -> Some v
                    | None -> search pe
              in
              search e
      in
      let stmts, e' = match src_opt with
        | None -> ([], e)
        | Some src_expr -> assign_with_cast e gid 0 dp `Out src_expr in
      (acc_stmts @ stmts, e')
    ) edges_to_compound ([], env)

(** [lower_graph env parent_gr compound_nid gr gid] translates an IF1 graph into a list of C statements. *)
let rec lower_graph env parent_gr compound_nid gr gid =
  let env = { env with curr_gid = gid; curr_gr = gr } in
  let env = scan_fanout gr gid env in
  let pre_decl_stmts, env = pre_declare_graph_locals env gr gid in
  let b_in_stmts, env =
    if env.parent_env = None || IntMap.mem gid env.proc_map then ([], env)
    else init_boundary_ports env parent_gr compound_nid gr gid in

  let sorted_nodes = topo_sort gr in
  let res_stmts, final_env = List.fold_left (fun (acc_stmts, e) nid ->
    if nid = 0 then (acc_stmts, e)
    else match NM.find_opt nid gr.nmap with
    | Some (Literal (_, code, value, _)) ->
        let lit = match code with | REAL | DOUBLE -> C.LitFloat (float_of_string value) | BOOLEAN -> C.Id (String.lowercase_ascii value) | _ -> try C.LitInt (int_of_string value) with _ -> C.LitInt 0 in
        let stmts, e' = assign_with_cast e gid nid 0 `Out lit in
        (acc_stmts @ stmts, e')
    | Some node ->
        let node_stmts, e' = lower_node e gr nid node in
        (acc_stmts @ node_stmts, e')
    | None -> (acc_stmts, e)
  ) (b_in_stmts, env) sorted_nodes in
  (pre_decl_stmts @ res_stmts, final_env)

and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, _ty, pr, loop_gr, _) ->
      let sub_gid = try GidMap.find (gid, nid) env.gid_table with _ -> -1 in
      let c_of = get_compound_type pr in
      if c_of = If1_forall then lower_forall env gr gid nid loop_gr sub_gid pr
      else if c_of = If1_predicate || c_of = If1_if then lower_if_graph env gr nid loop_gr sub_gid
      else if c_of = If1_loop_initial then lower_for_initial env gr gid nid loop_gr sub_gid pr
      else begin
        let decl_stmts, env = declare_outputs env gr gid nid node in
        let env_child = { env with parent_env = Some env; compound_nid_in_parent = nid; parent_map = IntMap.add sub_gid (gid, nid) env.parent_map } in
        let body, env_after = lower_graph env_child gr nid loop_gr sub_gid in
        let out_pids = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
        let res_prop, final_env = List.fold_left (fun (acc, e) dp ->
          let src_opt =
            match FullPortMap.find_opt (sub_gid, 0, dp, `In) env_after.var_map with
            | Some _ as found -> found
            | None ->
                (* boundary In ports aren't populated in var_map by lower_graph;
                   trace via sub-graph eset to find the producing node *)
                (match ES.fold (fun (src, dst, _) a -> if dst = (0, dp) then Some src else a) loop_gr.eset None with
                 | Some (sn, sp) -> FullPortMap.find_opt (sub_gid, sn, sp, `Out) env_after.var_map
                 | None -> None) in
          match src_opt with
          | Some src_expr ->
              let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
              (acc @ stmts, e')
          | None -> (acc, e)
        ) ([], { env_after with curr_gid = gid; curr_gr = gr; seen_decls = env_after.seen_decls }) out_pids in
        (decl_stmts @ [ C.Compound (body @ res_prop) ], final_env)
      end
  | Simple (_, sym, pin, pout, pr) -> lower_simple env gr nid sym pin pout pr
  | Literal _ -> ([], env)
  | _ -> failwith (Printf.sprintf "Unsupported IF1 node type at gid=%d nid=%d" gid nid)

and lower_simple env gr nid sym pin pout pr =
  let gid = env.curr_gid in
  let get_in_expr p =
    let producers = ES.fold (fun (src, dst, _) acc -> if dst = (nid, p) then Some src else acc) gr.eset None in
    match producers with
    | Some (sn, sp) ->
        let ty = get_final_ty env gid nid p `In in
        C.Call ("SISAL_CAST", [ C.Id (string_of_c_type ty); get_expr env gid sn sp `Out ])
    | None -> C.LitInt 0 in
  let e1 = get_in_expr 0 in let e2 = get_in_expr 1 in
  let t_res = get_final_ty env gid nid 0 `Out in
  let rhs = match sym with
  | ADD -> if t_res = C.Basic "sisal_array_t" then C.Call ("sisal_array_add", [ e1; e2 ]) else C.BinOp (C.Add, e1, e2)
  | SUBTRACT -> if t_res = C.Basic "sisal_array_t" then C.Call ("sisal_array_sub", [ e1; e2 ]) else C.BinOp (C.Sub, e1, e2)
  | TIMES -> if t_res = C.Basic "sisal_array_t" then C.Call ("sisal_array_mul", [ e1; e2 ]) else C.BinOp (C.Mul, e1, e2)
  | EQUAL -> C.BinOp (C.Eq, e1, e2)
  | NOT_EQUAL -> C.BinOp (C.Ne, e1, e2)
  | NOT -> C.UnaryOp (C.LogNot, e1)
  | NEGATE -> C.UnaryOp (C.Negate, e1)
  | ERROR_NODE -> C.LitFloat 0.0
  | OR -> C.BinOp (C.LogOr, e1, e2)
  | AND -> C.BinOp (C.LogAnd, e1, e2)
  | SHL -> C.BinOp (C.Shl, e1, e2)
  | ASHR -> C.BinOp (C.Shr, e1, e2)
  | BITAND -> C.BinOp (C.BitAnd, e1, e2)
  | BITOR -> C.BinOp (C.BitOr, e1, e2)
  | BITXOR -> C.BinOp (C.BitXor, e1, e2)
  | IDIVIDE | FDIVIDE -> C.BinOp (C.Div, e1, e2)
  | GREATER -> C.BinOp (C.Gt, e1, e2)
  | GREATER_EQUAL -> C.BinOp (C.Ge, e1, e2)
  | LESSER -> C.BinOp (C.Lt, e1, e2)
  | LESSER_EQUAL -> C.BinOp (C.Le, e1, e2)
  | AELEMENT | DV_ELEMENT | DV_LOAD_LINEAR ->
      let elem_ty = get_final_ty env gid nid 0 `Out in
      let cast_ptr = C.Cast (C.Pointer (elem_ty, []), C.Member (e1, "data")) in
      let idx = if sym = DV_LOAD_LINEAR then e2 else C.BinOp (C.Sub, e2, C.Member (e1, "lower_bound")) in
      C.Index (cast_ptr, idx)
  | RANGEGEN -> C.BinOp (C.Add, C.BinOp (C.Sub, e2, e1), C.LitInt 1)
  | ASIZE | DV_SCATTER -> C.Cast (C.Basic "int32_t", C.Member (e1, "size"))
  | ALIML -> C.Cast (C.Basic "int32_t", C.Member (e1, "lower_bound"))
  | ALIMH -> C.Cast (C.Basic "int32_t", C.BinOp (C.Sub, C.BinOp (C.Add, C.Member (e1, "lower_bound"), C.Cast (C.Basic "int64_t", C.Member (e1, "size"))), C.LitInt 1))
  | DV_NUM_RANK -> C.Member (e1, "rank")
  | DV_DIMENSION -> C.Call ("sisal_dv_dimension", [ e2; e1 ])
  | DV_OFFSET_AT -> C.Call ("sisal_dv_offset_at", [ e1; e2; get_in_expr 2 ])
  | DV_RESHAPE_BY_SHAPE -> C.Call ("sisal_array_reshape_by_shape", [ e1; e2 ])
  | TYPECAST -> e1
  | RELEMENTS -> e2
  | DOT | INNERPRODUCT_NODE ->
      let in_ty = get_final_ty env gid nid 0 `In in
      if in_ty = C.Basic "sisal_array_t" then
        C.Call ("sisal_array_innerproduct", [ e1; e2 ])
      else
        failwith (Printf.sprintf "DOT/INNERPRODUCT for non-DV types not supported at gid=%d nid=%d" gid nid)
  | DV_COMPRESS -> C.Call ("sisal_array_compress", [ e1; e2 ])
  | DV_SORT -> C.Call ("sisal_array_sort", [ e1 ])
  | DV_REVERSE -> C.Call ("sisal_array_reverse", [ e1 ])
  | DV_ROTATE -> C.Call ("sisal_array_rotate", [ e1; e2 ])
  | DV_SLICE -> C.Call ("sisal_array_slice", [ e1; e2; get_in_expr 2 ])
  | DV_PERMUTE -> C.Call ("sisal_array_permute", [ e1; e2 ])
  | ASETL -> C.Call ("sisal_array_setl", [ e1; C.Cast (C.Basic "int64_t", e2) ])
  | AREPLACE ->
      let e3 = get_in_expr 2 in
      let val_ty = get_final_ty env gid nid 2 `In in
      let fn = match val_ty with
        | C.Basic "int32_t" | C.Basic "bool" -> "sisal_array_replace_i32"
        | C.Basic "double" -> "sisal_array_replace_f64"
        | C.Basic "sisal_array_t" -> "sisal_array_replace_arr"
        | _ -> "sisal_array_replace_f32" in
      C.Call (fn, [ e1; C.Cast (C.Basic "int64_t", e2); e3 ])
  | PAD_NODE -> C.Call ("sisal_array_pad", [ e1; e2; get_in_expr 2; get_in_expr 3 ])
  | STENCIL_NODE -> C.Call ("sisal_array_stencil", [ e1; e2; get_in_expr 2 ])
  | WHERE_NODE -> C.Call ("sisal_array_where", [ e1; e2; get_in_expr 2 ])
  | NONZERO_NODE -> C.Call ("sisal_array_nonzero", [ e1 ])
  | REDUCE_ALL ->
      let fname = List.find_map (function Name n -> Some n | _ -> None) pr |> Option.map String.lowercase_ascii |> Option.value ~default:"sum" in
      let reduce_fn = match (fname, t_res) with
        | ("sum", C.Basic "double") -> "sisal_array_reduce_double_sum"
        | ("sum", C.Basic "float") -> "sisal_array_reduce_sum"
        | ("sum", C.Basic "int32_t") -> "sisal_array_reduce_int_sum"
        | ("product", C.Basic "double") -> "sisal_array_reduce_double_product"
        | ("product", C.Basic "float") -> "sisal_array_reduce_float_product"
        | ("product", C.Basic "int32_t") -> "sisal_array_reduce_int_product"
        | ("least", C.Basic "double") -> "sisal_array_reduce_double_least"
        | ("least", C.Basic "float") -> "sisal_array_reduce_least"
        | ("least", C.Basic "int32_t") -> "sisal_array_reduce_int_least"
        | ("greatest", C.Basic "double") -> "sisal_array_reduce_double_greatest"
        | ("greatest", C.Basic "float") -> "sisal_array_reduce_greatest"
        | ("greatest", C.Basic "int32_t") -> "sisal_array_reduce_int_greatest"
        | _ -> "sisal_array_reduce_double_sum" in
      C.Call (reduce_fn, [e1])
  | INVOCATION ->
      let fname_pragma = List.find_map (function Name n -> Some n | _ -> None) pr in
      let fname, start_port = match fname_pragma with
        | Some n -> ("func_" ^ String.uppercase_ascii n, 0)
        | None ->
            (match ES.fold (fun (src, dst, _) acc -> if dst = (nid, 0) then Some src else acc) gr.eset None with
             | Some (0, pn) ->
                 (match IntMap.find_opt pn env.proc_map with
                  | Some name -> (name, 1)
                  | _ -> ("func_UNKNOWN", 1))
             | _ -> ("func_UNKNOWN", 1)) in
      let in_ports = ES.fold (fun (_, (dn, dp), _) acc -> if dn = nid then IntSet.add dp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
      let args = List.filter_map (fun pid -> if pid < start_port then None else Some (get_in_expr pid)) in_ports in
      C.Call (fname, args)
  | sym -> failwith (Printf.sprintf "Unsupported IF1 Simple node symbol at gid=%d nid=%d: %s" gid nid (string_of_node_sym sym)) in
  let stmts, e' = assign_with_cast env gid nid 0 `Out rhs in
  ( stmts, e' )

and lower_if_graph env parent_gr nid loop_gr loop_gid =
  let gid = env.curr_gid in
  let env_loop_base = { env with parent_env = Some env; compound_nid_in_parent = nid; curr_gid = loop_gid; curr_gr = loop_gr } in
  let env_loop_base = scan_fanout loop_gr loop_gid env_loop_base in
  let node = match NM.find_opt nid parent_gr.nmap with Some n -> n | _ -> failwith "no node" in
  let decl_stmts, env_loop_base = declare_outputs env_loop_base parent_gr gid nid node in
  let loop_in_stmts, env_loop = init_boundary_ports env_loop_base parent_gr nid loop_gr loop_gid in
  let pred_cid, pred_sg = match find_subgraph loop_gr "PREDICATE" with | Some x -> x | _ -> failwith "no PRED" in
  let pgid = try GidMap.find (loop_gid, pred_cid) env.gid_table with _ -> -1 in
  let env_pred = { env_loop with parent_env = Some env_loop; curr_gid = pgid; curr_gr = pred_sg; parent_map = IntMap.add pgid (loop_gid, pred_cid) env_loop.parent_map } in
  let pred_stmts, e_pred = lower_graph env_pred loop_gr pred_cid pred_sg pgid in
  let v_pred = match ES.fold (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc) pred_sg.eset None with
    | Some (sn, sp) -> get_expr e_pred pgid sn sp `Out
    | None -> C.LitInt 0 in
  let env_loop = { env_loop with var_map = e_pred.var_map; type_table = e_pred.type_table; seen_decls = e_pred.seen_decls } in
  let then_cid, then_sg = match find_subgraph loop_gr "THEN" with | Some x -> x | _ -> failwith "no THEN" in
  let tgid = try GidMap.find (loop_gid, then_cid) env.gid_table with _ -> -1 in
  let env_then = { env_loop with parent_env = Some env_loop; curr_gid = tgid; curr_gr = then_sg; parent_map = IntMap.add tgid (loop_gid, then_cid) env_loop.parent_map } in
  let then_stmts, e_then = lower_graph env_then loop_gr then_cid then_sg tgid in
  let else_cid, else_sg = match find_subgraph loop_gr "ELSE" with | Some x -> x | _ -> failwith "no ELSE" in
  let egid = try GidMap.find (loop_gid, else_cid) env.gid_table with _ -> -1 in
  let env_else = { env_loop with parent_env = Some env_loop; curr_gid = egid; curr_gr = else_sg; parent_map = IntMap.add egid (loop_gid, else_cid) env_loop.parent_map } in
  let else_stmts, e_else = lower_graph env_else loop_gr else_cid else_sg egid in
  let if_out_pids = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) parent_gr.eset IntSet.empty |> IntSet.elements in
  let then_props, e_final_then = List.fold_left (fun (acc, e) dp ->
    let src_opt = match FullPortMap.find_opt (tgid, 0, dp, `In) e_then.var_map with
      | Some _ as found -> found
      | None ->
          (match ES.fold (fun (src, dst, _) a -> if dst = (0, dp) then Some src else a) then_sg.eset None with
           | Some (sn, sp) -> FullPortMap.find_opt (tgid, sn, sp, `Out) e_then.var_map
           | None -> None) in
    match src_opt with
    | Some src_expr ->
        let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
        (acc @ stmts, e')
    | None -> (acc, e)
  ) ([], { e_then with curr_gid = gid; curr_gr = parent_gr }) if_out_pids in
  let else_props, e_final_else = List.fold_left (fun (acc, e) dp ->
    let src_opt = match FullPortMap.find_opt (egid, 0, dp, `In) e_else.var_map with
      | Some _ as found -> found
      | None ->
          (match ES.fold (fun (src, dst, _) a -> if dst = (0, dp) then Some src else a) else_sg.eset None with
           | Some (sn, sp) -> FullPortMap.find_opt (egid, sn, sp, `Out) e_else.var_map
           | None -> None) in
    match src_opt with
    | Some src_expr ->
        let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
        (acc @ stmts, e')
    | None -> (acc, e)
  ) ([], { e_else with curr_gid = gid; curr_gr = parent_gr }) if_out_pids in
  let if_stmt = C.If (v_pred, then_stmts @ then_props, else_stmts @ else_props) in
  (* Note: We union the seen_decls from both branches to avoid duplicate declarations later *)
  let final_seen = StringSet.union e_final_then.seen_decls e_final_else.seen_decls in
  (decl_stmts @ loop_in_stmts @ [ C.Compound (pred_stmts @ [ if_stmt ]) ], { e_final_else with seen_decls = final_seen })

and lower_forall env gr gid nid loop_gr sub_gid pr =
  let env_init = { env with parent_env = Some env; compound_nid_in_parent = nid; curr_gid = sub_gid; curr_gr = loop_gr } in
  let env_init = scan_fanout loop_gr sub_gid env_init in
  let node = match NM.find_opt nid gr.nmap with Some n -> n | _ -> failwith "no node" in
  let decl_stmts, env_init = declare_outputs env_init gr gid nid node in
  let loop_in_stmts, env_loop = init_boundary_ports env_init gr nid loop_gr sub_gid in
  let gen_nid, gen_gr = match find_subgraph loop_gr "GENERATOR" with | Some x -> x | _ -> failwith "no GEN" in
  let gen_gid = try GidMap.find (sub_gid, gen_nid) env.gid_table with _ -> -1 in
  let env_gen = { env_loop with parent_env = Some env_loop; curr_gid = gen_gid; curr_gr = gen_gr; parent_map = IntMap.add gen_gid (sub_gid, gen_nid) env_loop.parent_map } in
  let gen_stmts, e_gen = lower_graph env_gen loop_gr gen_nid gen_gr gen_gid in
  let count = match ES.fold (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc) gen_gr.eset None with
    | Some (sn, sp) -> get_expr e_gen gen_gid sn sp `Out
    | None -> C.LitInt 0 in
  let env_loop = { env_loop with var_map = e_gen.var_map; type_table = e_gen.type_table; seen_decls = e_gen.seen_decls } in

  let body_nid, body_gr = match find_subgraph loop_gr "BODY" with | Some x -> x | _ -> failwith "no BODY" in
  let body_gid = try GidMap.find (sub_gid, body_nid) env.gid_table with _ -> -1 in
  let idx_port = ES.fold (fun ((sn, _), (dn, dp), _) acc -> if sn = gen_nid && dn = body_nid then Some dp else acc) loop_gr.eset None |> Option.value ~default:0 in
  let loop_idx_var = Printf.sprintf "__idx_%s" (scope_of env.gid_name_map sub_gid) in
  (* Lower bound from GENERATOR node 1 (the literal that feeds RANGEGEN port 0). *)
  let lb_expr = match FullPortMap.find_opt (gen_gid, 1, 0, `Out) e_gen.var_map with
    | Some ex -> ex | None -> C.LitInt 0 in
  (* Wire any loop_gr boundary ports that weren't provided by the parent graph.
     Standard forall: loop variable = lb + loop_counter (index-based).
     DV element forall ("for i in A dot j in B"): loop variable = A.data[loop_counter] (element). *)
  let env_loop =
    let loop_local_cs, _ = loop_gr.symtab in
    let is_dv_elem_forall =
      NM.exists (fun _ n -> match n with Simple (_, DV_SCATTER, _, _, _) -> true | _ -> false) gen_gr.nmap in
    if is_dv_elem_forall then begin
      (* Pair array inputs with loop variables by sort order of boundary port number. *)
      let tm = get_typemap_tm loop_gr in
      let arr_syms = SM.fold (fun _ v acc ->
        if v.val_def = 0 then match TM.find_opt v.val_ty tm with
          | Some (Array_dv _) | Some (Array_ty _) -> (v.def_port, v.val_ty) :: acc | _ -> acc
        else acc) loop_local_cs [] |> List.sort compare in
      let var_syms = SM.fold (fun _ v acc ->
        if v.val_def = 0 then match TM.find_opt v.val_ty tm with
          | Some (Basic _) -> (v.def_port, v.val_ty) :: acc | _ -> acc
        else acc) loop_local_cs [] |> List.sort compare in
      List.fold_left2 (fun e (arr_port, _) (var_port, var_ty_id) ->
        if FullPortMap.mem (sub_gid, 0, var_port, `Out) e.var_map then e
        else
          let arr_expr = match FullPortMap.find_opt (sub_gid, 0, arr_port, `Out) e.var_map with
            | Some ex -> ex | None -> C.LitInt 0 in
          let elem_if1_ty = try TM.find var_ty_id tm with _ -> Basic INTEGRAL in
          let elem_ty = c_type_of_if1_ty tm elem_if1_ty in
          let elem_expr = C.Index (C.Cast (C.Pointer (elem_ty, []), C.Member (arr_expr, "data")), C.Id loop_idx_var) in
          { e with var_map = FullPortMap.add (sub_gid, 0, var_port, `Out) elem_expr e.var_map }
      ) env_loop arr_syms var_syms
    end else
      SM.fold (fun _ v e ->
        if v.val_def = 0 && not (FullPortMap.mem (sub_gid, 0, v.def_port, `Out) e.var_map) then
          let loop_var_expr = C.BinOp (C.Add, lb_expr, C.Id loop_idx_var) in
          { e with var_map = FullPortMap.add (sub_gid, 0, v.def_port, `Out) loop_var_expr e.var_map }
        else e
      ) loop_local_cs env_loop in

  (* Identify the body boundary output port that holds the array element (non-BOOLEAN type).
     DV FORALLs have two body outputs: LFCOMPAT (bool, type_id 1) and LFDRES (element).
     Port ordering varies; find the non-boolean port so we accumulate the right value. *)
  let body_elem_port, body_elem_type_id =
    match ES.fold (fun (_, (dn, dp), t) acc ->
      if dn = 0 && t <> 1 then Some (dp, t) else acc) body_gr.eset None with
    | Some (p, t) -> (p, t)
    | None ->
      (match ES.fold (fun (_, (dn, dp), t) acc ->
        if dn = 0 then Some (dp, t) else acc) body_gr.eset None with
      | Some (p, t) -> (p, t)
      | None -> (0, 6)) in
  let fold_op = forall_fold_op loop_gr in
  let stmts_alloc, e_alloc = assign_with_cast env_loop gid nid 0 `Out (C.LitInt 0) in
  let res_v = match FullPortMap.find_opt (gid, nid, 0, `Out) e_alloc.var_map with Some (C.Id n) -> C.Id n | _ -> C.Id (get_c_name env.proc_map env.gid_name_map gid nid 0 `Out gr) in
  let tid =
    match get_elem_type env env.curr_gr nid with
    | Unknown_ty -> body_elem_type_id
    | ty -> (try find_ty_safe env.curr_gr ty with _ -> body_elem_type_id) in
  let env_body = { e_alloc with parent_env = Some e_alloc; curr_gid = body_gid; curr_gr = body_gr; parent_map = IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map } in
  let env_body = { env_body with var_map = FullPortMap.add (body_gid, 0, idx_port, `Out) (C.Id loop_idx_var) env_body.var_map } in
  (* Pre-seed __LFI in BODY scope: block pre_declare from zeroing it, emit explicit decl with lb+idx *)
  let lfi_stmt_opt, env_body =
    let cs, _ = body_gr.symtab in
    SM.fold (fun _ v (stmt_acc, e) ->
      if stmt_acc <> None then (stmt_acc, e)
      else if v.val_name = "__LFI" && v.val_def = 0 then
        let lfi_name = Printf.sprintf "v_%s_n__0___LFI" (scope_of env.gid_name_map body_gid) in
        let decl = C.Decl (C.Basic "int32_t", lfi_name,
          Some (C.BinOp (C.Add, lb_expr, C.Id loop_idx_var))) in
        let e' = { e with
          seen_decls = StringSet.add lfi_name e.seen_decls;
          var_map = FullPortMap.add (body_gid, 0, v.def_port, `Out) (C.Id lfi_name) e.var_map } in
        (Some decl, e')
      else (stmt_acc, e)
    ) cs (None, env_body) in
  let lfi_stmts = match lfi_stmt_opt with Some s -> [s] | None -> [] in
  let body_stmts, e_body = lower_graph env_body loop_gr body_nid body_gr body_gid in
  let out_ty = get_final_ty e_body body_gid 0 body_elem_port `In in
  let body_res = match ES.fold (fun (src, (dn, dp), _) acc -> if dn = 0 && dp = body_elem_port then Some src else acc) body_gr.eset None with
    | Some (sn, sp) -> get_expr e_body body_gid sn sp `Out
    | None -> C.LitInt 0 in
  let cast_body_res = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type out_ty); body_res ]) in
  let out_pids = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
  match fold_op with
  | Some op_name ->
      (* Fold (returns value of sum/product/least/greatest): accumulate a scalar, no array needed. *)
      let acc_var = Printf.sprintf "__acc_%s" (scope_of env.gid_name_map sub_gid) in
      let init_val = match (op_name, out_ty) with
        | ("product", _) -> C.LitInt 1
        | ("least",  C.Basic "double") -> C.Id "1e308"
        | ("least",  C.Basic "float")  -> C.Id "3.4028235e+38f"
        | ("least",  _)                -> C.Id "0x7fffffff"
        | ("greatest", C.Basic "double") -> C.UnaryOp (C.Negate, C.Id "1e308")
        | ("greatest", C.Basic "float")  -> C.UnaryOp (C.Negate, C.Id "3.4028235e+38f")
        | ("greatest", _)                -> C.UnaryOp (C.Negate, C.Id "0x7fffffff")
        | _ -> C.LitInt 0 in
      let acc_decl = C.Decl (out_ty, acc_var, Some init_val) in
      let update = match op_name with
        | "product" -> C.BinOp (C.Assign, C.Id acc_var, C.BinOp (C.Mul, C.Id acc_var, cast_body_res))
        | "least"   -> C.BinOp (C.Assign, C.Id acc_var,
            C.Call ("SISAL_CAST", [ C.Id (string_of_c_type out_ty);
              C.BinOp (C.Lt, cast_body_res, C.Id acc_var) |> fun cond ->
                C.Call ("SISAL_CAST", [C.Id (string_of_c_type out_ty);
                  C.BinOp (C.Add,
                    C.BinOp (C.Mul, cond, cast_body_res),
                    C.BinOp (C.Mul, C.UnaryOp (C.LogNot, cond), C.Id acc_var))]) ]))
        | "greatest" -> C.BinOp (C.Assign, C.Id acc_var,
            C.Call ("SISAL_CAST", [ C.Id (string_of_c_type out_ty);
              C.BinOp (C.Gt, cast_body_res, C.Id acc_var) |> fun cond ->
                C.Call ("SISAL_CAST", [C.Id (string_of_c_type out_ty);
                  C.BinOp (C.Add,
                    C.BinOp (C.Mul, cond, cast_body_res),
                    C.BinOp (C.Mul, C.UnaryOp (C.LogNot, cond), C.Id acc_var))]) ]))
        | _ (* sum *) ->
            let upd_op = if out_ty = C.Basic "bool" then C.LogOr else C.Add in
            C.BinOp (C.Assign, C.Id acc_var, C.BinOp (upd_op, C.Id acc_var, cast_body_res)) in
      let loop = C.For (C.Decl (C.Basic "int32_t", loop_idx_var, Some (C.LitInt 0)), C.BinOp (C.Lt, C.Id loop_idx_var, count), C.BinOp (C.Assign, C.Id loop_idx_var, C.BinOp (C.Add, C.Id loop_idx_var, C.LitInt 1)), lfi_stmts @ body_stmts @ [ C.Expr update ]) in
      let assign_result_stmts, final_env =
        let stmts, e' = assign_with_cast { e_body with curr_gid = gid; curr_gr = gr } gid nid 0 `Out (C.Id acc_var) in
        (stmts, e') in
      (decl_stmts @ [ C.Compound (loop_in_stmts @ gen_stmts @ stmts_alloc @ [ acc_decl; loop ] @ assign_result_stmts) ], final_env)
  | None ->
      (* Gather (returns array of / returns array_dv of): collect into an array. *)
      let alloc = C.Expr (C.BinOp (C.Assign, res_v, C.Call ("sisal_array_alloc_empty", [ C.LitInt 1; C.LitInt tid; C.Cast (C.Basic "uint64_t", count) ]))) in
      let store = C.Expr (C.BinOp (C.Assign, C.Index (C.Cast (C.Pointer (out_ty, []), C.Member (res_v, "data")), C.Id loop_idx_var), cast_body_res)) in
      let loop = C.For (C.Decl (C.Basic "int32_t", loop_idx_var, Some (C.LitInt 0)), C.BinOp (C.Lt, C.Id loop_idx_var, count), C.BinOp (C.Assign, C.Id loop_idx_var, C.BinOp (C.Add, C.Id loop_idx_var, C.LitInt 1)), lfi_stmts @ body_stmts @ [ store ]) in
      let props, final_env = List.fold_left (fun (acc, e) dp ->
        if dp = 0 then (acc, e)
        else match FullPortMap.find_opt (body_gid, 0, dp, `In) e_body.var_map with
        | Some src_expr ->
            let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
            (acc @ stmts, e')
        | None -> (acc, e)
      ) ([], { e_body with curr_gid = gid; curr_gr = gr }) out_pids in
      (decl_stmts @ [ C.Compound (loop_in_stmts @ gen_stmts @ stmts_alloc @ [ alloc; loop ] @ props) ], final_env)

and lower_for_initial env gr gid nid loop_gr sub_gid pr =
  let env_init_base = { env with parent_env = Some env; compound_nid_in_parent = nid; curr_gid = sub_gid; curr_gr = loop_gr } in
  let env_init_base = scan_fanout loop_gr sub_gid env_init_base in
  let node = match NM.find_opt nid gr.nmap with Some n -> n | _ -> failwith "no node" in
  let decl_stmts, env_init_base = declare_outputs env_init_base gr gid nid node in
  let loop_in_stmts, env_loop = init_boundary_ports env_init_base gr nid loop_gr sub_gid in
  let init_nid, init_gr = match find_subgraph loop_gr "INIT" with | Some x -> x | _ -> failwith "no INIT" in
  let init_gid = try GidMap.find (sub_gid, init_nid) env.gid_table with _ -> -1 in
  let env_init = { env_loop with parent_env = Some env_loop; curr_gid = init_gid; curr_gr = init_gr; parent_map = IntMap.add init_gid (sub_gid, init_nid) env_loop.parent_map } in
  let init_stmts, e_init = lower_graph env_init loop_gr init_nid init_gr init_gid in
  let env_loop = { env_loop with var_map = e_init.var_map; type_table = e_init.type_table; seen_decls = e_init.seen_decls } in
  let test_nid, test_gr = match find_subgraph loop_gr "TEST" with | Some x -> x | _ -> failwith "no TEST" in
  let test_gid = try GidMap.find (sub_gid, test_nid) env.gid_table with _ -> -1 in
  let env_test = { env_loop with parent_env = Some env_loop; curr_gid = test_gid; curr_gr = test_gr; parent_map = IntMap.add test_gid (sub_gid, test_nid) env_loop.parent_map } in
  let test_stmts, e_test = lower_graph env_test loop_gr test_nid test_gr test_gid in
  let cond = match ES.fold (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc) test_gr.eset None with
    | Some (sn, sp) -> get_expr e_test test_gid sn sp `Out
    | None -> C.LitInt 0 in
  let env_loop = { env_loop with var_map = e_test.var_map; type_table = e_test.type_table; seen_decls = e_test.seen_decls } in
  let body_nid, body_gr = match find_subgraph loop_gr "BODY" with | Some x -> x | _ -> failwith "no BODY" in
  let body_gid = try GidMap.find (sub_gid, body_nid) env.gid_table with _ -> -1 in
  let env_body = { env_loop with parent_env = Some env_loop; curr_gid = body_gid; curr_gr = body_gr; parent_map = IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map } in
  let body_stmts, e_body = lower_graph env_body loop_gr body_nid body_gr body_gid in
  let env_loop = { env_loop with var_map = e_body.var_map; type_table = e_body.type_table; seen_decls = e_body.seen_decls } in
  let while_loop = C.While (cond, body_stmts @ test_stmts) in
  let ret_nid, ret_gr = match find_subgraph loop_gr "RETURNS" with | Some x -> x | _ -> failwith "no RET" in
  let ret_gid = try GidMap.find (sub_gid, ret_nid) env.gid_table with _ -> -1 in
  let env_ret = { env_loop with parent_env = Some env_loop; curr_gid = ret_gid; curr_gr = ret_gr; parent_map = IntMap.add ret_gid (sub_gid, ret_nid) env_loop.parent_map } in
  let ret_stmts, e_ret = lower_graph env_ret loop_gr ret_nid ret_gr ret_gid in
  let out_pids = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
  let props, final_env = List.fold_left (fun (acc, e) dp ->
    match FullPortMap.find_opt (ret_gid, 0, dp, `In) e_ret.var_map with
    | Some src_expr -> 
        let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
        (acc @ stmts, e')
    | None -> (acc, e)
  ) ([], { e_ret with curr_gid = gid; curr_gr = gr }) out_pids in
  (decl_stmts @ [ C.Compound (loop_in_stmts @ init_stmts @ test_stmts @ [ while_loop ] @ ret_stmts @ props) ], final_env)

let dummy_env tm sub_gr = { tm; var_map = FullPortMap.empty; type_table = FullPortMap.empty; preds = FullPortMap.empty; curr_gid = 0; curr_gr = sub_gr; parent_env = None; compound_nid_in_parent = 0; seen_decls = StringSet.empty; fanout_map = PortFanout.empty; mandatory_ports = PortSet.empty; gid_table = GidMap.empty; parent_map = IntMap.empty; proc_map = IntMap.empty; proc_param_map = FullPortMap.empty; gid_name_map = IntMap.empty; procedures_info = IntMap.empty; force_gpu = false }


let lower_procedure tm gid_table gid_name_map proc_map procedures_info_map nid node gr_module =
  match node with
  | Compound (_, INTERNAL, ty_id, pr, sub_gr, _) ->
      let func_name = List.find_map (function Name nm -> Some nm | _ -> None) pr |> Option.map String.uppercase_ascii |> Option.map (fun n -> "func_" ^ n) |> Option.value ~default:"unnamed" in

      let all_b_ins = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) -> List.init (List.length ins) (fun i -> i)
        | _ -> [] in
      let env_module = { (dummy_env tm gr_module) with gid_table; proc_map; gid_name_map; procedures_info = procedures_info_map; curr_gid = 0; curr_gr = gr_module } in
      let env_init = { (dummy_env tm sub_gr) with gid_table; proc_map; gid_name_map; procedures_info = procedures_info_map; curr_gid = nid; parent_env = Some env_module } in

      (* Seed the procedure types using the function's type definition *)
      let param_types = get_function_param_types tm ty_id in
      let env_seeded = List.fold_left2 (fun env_acc pid tid ->
        let ty_val = try TM.find tid tm with _ -> Basic REAL in
        { env_acc with type_table = FullPortMap.add (nid, 0, pid, `Out) (c_type_of_if1_ty tm ty_val) env_acc.type_table }
      ) env_init (List.filter (fun p -> p < List.length param_types) all_b_ins) param_types in

      let env_typed = infer_types env_seeded sub_gr nid in
      let param_tids = get_function_param_types tm ty_id in
      let params = List.mapi (fun i pid ->
        let ty =
          if i < List.length param_tids then
            let tid = List.nth param_tids i in
            let ty_val = try TM.find tid tm with _ -> Basic REAL in
            c_type_of_if1_ty tm ty_val
          else get_final_ty env_typed nid 0 pid `Out in
        let name = match get_port_name_from_cs sub_gr 0 pid `Out with | Some n -> sanitize n | None -> Printf.sprintf "param_%d" pid in
        (ty, name)
      ) all_b_ins in
      (* Seed param names so pre_declare sees them and can detect conflicts *)
      let env_param_seeded = List.fold_left2 (fun e pid (_, name) -> { e with var_map = FullPortMap.add (nid, 0, pid, `Out) (C.Id name) e.var_map; seen_decls = StringSet.add name e.seen_decls }) env_typed all_b_ins params in

      (* Pre-declare all locals up front; this overwrites boundary-input entries in var_map
         with the local variable names (e.g. v_g1_n__0_V instead of V) *)
      let pre_stmts, env_predecl = pre_declare_graph_locals env_param_seeded sub_gr nid in

      (* Bind each function parameter to its newly-created local declaration *)
      let bind_stmts = List.concat (List.mapi (fun i (ty, param_name) ->
        match FullPortMap.find_opt (nid, 0, i, `Out) env_predecl.var_map with
        | Some (C.Id local_name) when local_name <> param_name ->
            [ C.Expr (C.BinOp (C.Assign, C.Id local_name,
                C.Call ("SISAL_CAST", [C.Id (string_of_c_type ty); C.Id param_name]))) ]
        | _ -> []
      ) params) in
      (* Bind alias symtab entries (same port, different val_name) to the canonical variable *)
      let alias_bind_stmts =
        let cs, _ = sub_gr.symtab in
        SM.fold (fun _ v acc ->
          if is_proc_expr env_predecl nid v.val_def then acc
          else
            let specific = Printf.sprintf "v_%s_n__%d_%s"
              (scope_of gid_name_map nid) v.val_def (sanitize v.val_name) in
            match FullPortMap.find_opt (nid, v.val_def, v.def_port, `Out) env_predecl.var_map with
            | Some (C.Id canonical) when canonical <> specific
                && StringSet.mem specific env_predecl.seen_decls ->
                let ty = get_final_ty env_predecl nid v.val_def v.def_port `Out in
                acc @ [ C.Expr (C.BinOp (C.Assign, C.Id specific,
                    C.Call ("SISAL_CAST", [C.Id (string_of_c_type ty); C.Id canonical]))) ]
            | _ -> acc
        ) cs [] in

      (* Determine output ports and declare their return variables up front, just like
         boundary inputs, so they are visible for the whole procedure body.
         Exclude error edges (BROADCAST_ERROR etc.) — those are exception flows, not return values. *)
      let out_pids = ES.fold (fun (_, (dn, dp), ty) acc -> if dn = 0 && not (is_error_port ty sub_gr) then IntSet.add dp acc else acc) sub_gr.eset IntSet.empty |> IntSet.elements in
      let ret_decl_stmts, env_predecl = List.fold_left (fun (acc_stmts, e) pid ->
        let ty = get_final_ty e nid 0 pid `In in
        let name = get_c_name e.proc_map e.gid_name_map nid 0 pid `In sub_gr in
        if not (StringSet.mem name e.seen_decls) then
          let init_val = if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
          (acc_stmts @ [ C.Decl (ty, name, init_val) ],
           { e with seen_decls = StringSet.add name e.seen_decls;
                    var_map = FullPortMap.add (nid, 0, pid, `In) (C.Id name) e.var_map })
        else
          (acc_stmts, e)
      ) ([], env_predecl) out_pids in

      (* lower_graph will call pre_declare_graph_locals again, but seen_decls already has
         all names, so it produces no new decls — body is purely the node computations *)
      let body, env_after = lower_graph env_predecl sub_gr nid sub_gr nid in

      (* Assign computed results into the pre-declared return variables *)
      let ret_assign_stmts = List.filter_map (fun pid ->
        let ty = get_final_ty env_after nid 0 pid `In in
        let ret_name = get_c_name env_after.proc_map env_after.gid_name_map nid 0 pid `In sub_gr in
        match ES.fold (fun (src, dst, _) acc -> if dst = (0, pid) then Some src else acc) sub_gr.eset None with
        | Some (sn, sp) ->
            let src_expr = get_expr env_after nid sn sp `Out in
            Some (C.Expr (C.BinOp (C.Assign, C.Id ret_name,
                C.Call ("SISAL_CAST", [C.Id (string_of_c_type ty); src_expr]))))
        | None -> None
      ) out_pids in

      let res_struct_name = (String.uppercase_ascii func_name) ^ "_results" in
      if List.length out_pids = 1 then
        let pid = List.hd out_pids in
        let ty = get_final_ty env_after nid 0 pid `In in
        let ret_name = get_c_name env_after.proc_map env_after.gid_name_map nid 0 pid `In sub_gr in
        let cast_ret = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type ty); C.Id ret_name ]) in
        { C.return_ty = ty; name = func_name; params; body = pre_stmts @ bind_stmts @ alias_bind_stmts @ ret_decl_stmts @ body @ ret_assign_stmts @ [ C.Return (Some cast_ret) ]; extern_c = true }
      else
        let res_obj_name = "__res_obj" in
        let assignments = List.map (fun pid ->
          let ty = get_final_ty env_after nid 0 pid `In in
          let ret_name = get_c_name env_after.proc_map env_after.gid_name_map nid 0 pid `In sub_gr in
          C.Expr (C.BinOp (C.Assign, C.Member (C.Id res_obj_name, "res_" ^ string_of_int pid),
                          C.Call ("SISAL_CAST", [ C.Id (string_of_c_type ty); C.Id ret_name ])))
        ) out_pids in
        { C.return_ty = C.Basic ("struct " ^ res_struct_name); name = func_name; params; body = pre_stmts @ bind_stmts @ alias_bind_stmts @ ret_decl_stmts @ body @ ret_assign_stmts @ [ C.Decl (C.Basic ("struct " ^ res_struct_name), res_obj_name, None) ] @ assignments @ [ C.Return (Some (C.Id res_obj_name)) ]; extern_c = true }
  | _ -> failwith "not compound"

let build_global_gid_table root_nid gr starting_gid =
  let table = Hashtbl.create 64 in
  let name_map = Hashtbl.create 64 in
  let rec visit parent_gid sub_gr counter =
    NM.fold (fun nid node ctr ->
      match node with
      | Compound (_, _, _, pr, inner_gr, _) ->
          let gid = ctr + 1 in
          Hashtbl.replace table (parent_gid, nid) gid;
          let cname = match List.find_map (function Name n -> Some (sanitize n) | _ -> None) pr with
            | Some n -> n
            | None -> "g" ^ string_of_int gid in
          Hashtbl.replace name_map gid cname;
          visit gid inner_gr gid
      | _ -> ctr) sub_gr.nmap counter
  in
  let final_counter = visit root_nid gr starting_gid in
  let gid_map = Hashtbl.fold (fun k v m -> GidMap.add k v m) table GidMap.empty in
  let nmap = Hashtbl.fold (fun k v m -> IntMap.add k v m) name_map IntMap.empty in
  (gid_map, final_counter, nmap)

let rec collect_all_records tm gr seen =
  let local_records, seen = TM.fold (fun id ty (acc, s) ->
    match ty with
    | Record (field_ty_id, next_label, name) ->
        if IntSet.mem id s then (acc, s)
        else
          let fields = collect_record_fields tm field_ty_id in
          (C.Type (C.Struct ("struct_rec_" ^ string_of_int id, fields)) :: acc, IntSet.add id s)
    | _ -> (acc, s)) tm ([], seen) in
  NM.fold (fun _ node (acc, s) -> match node with | Compound (_, _, _, _, sub, _) ->
      let _, sub_tm, _ = sub.typemap in
      let sub_recs, s' = collect_all_records sub_tm sub s in
      (acc @ sub_recs, s') | _ -> (acc, s)) gr.nmap (local_records, seen)

let lower_to_c tm gr filename =
  let procedures_info = NM.fold (fun nid node acc -> match node with | Compound (_, INTERNAL, _, pr, sub_gr, _) when get_compound_type pr = If1_procedure -> (nid, node, sub_gr) :: acc | _ -> acc) gr.nmap [] in
  let global_table, gid_name_map = List.fold_left (fun (acc_tbl, acc_names, next_gid) (nid, _, sub_gr) ->
    let tbl, last_gid, nmap = build_global_gid_table nid sub_gr next_gid in
    let acc_tbl = GidMap.add (0, nid) nid acc_tbl in
    let acc_names = IntMap.union (fun _ a _ -> Some a) acc_names nmap in
    (GidMap.fold (fun k v m -> GidMap.add k v m) tbl acc_tbl, acc_names, last_gid + 1000)
  ) (GidMap.empty, IntMap.empty, 10000) procedures_info |> (fun (t, n, _) -> (t, n)) in

  let proc_map = List.fold_left (fun m (nid, node, _) ->
    match node with
    | Compound (_, INTERNAL, _, pr, _, _) ->
        let func_name = List.find_map (function Name nm -> Some nm | _ -> None) pr |> Option.map String.uppercase_ascii |> Option.map (fun n -> "func_" ^ n) in
        (match func_name with Some n -> IntMap.add nid n m | None -> m)
    | _ -> m
  ) IntMap.empty procedures_info in

  let procedures_info_map = List.fold_left (fun m (nid, _, sub_gr) -> IntMap.add nid sub_gr m) IntMap.empty procedures_info in

  let procedures = List.map (fun (nid, node, sub_gr) ->
    let _, proc_tm, _ = sub_gr.typemap in
    lower_procedure proc_tm global_table gid_name_map proc_map procedures_info_map nid node gr
  ) procedures_info in

  let result_struct_decls = List.filter_map (fun (nid, node, sub_gr) -> match node with | Compound (_, INTERNAL, _, pr, _, _) ->
      let func_name = List.find_map (function Name nm -> Some nm | _ -> None) pr |> Option.map String.uppercase_ascii |> Option.map (fun n -> "func_" ^ n) |> Option.value ~default:"unnamed" in
      let out_pids = ES.fold (fun (_, (dn, dp), ty) acc -> if dn = 0 && not (is_error_port ty sub_gr) then IntSet.add dp acc else acc) sub_gr.eset IntSet.empty |> IntSet.elements in
      if List.length out_pids > 1 then
        let results = List.map (fun pid -> let env_tmp = { (dummy_env tm sub_gr) with curr_gr = sub_gr; gid_table = global_table; proc_map; gid_name_map; procedures_info = procedures_info_map; curr_gid = nid } in ("res_" ^ string_of_int pid, get_final_ty (infer_types env_tmp sub_gr nid) nid 0 pid `In)) out_pids in
        Some (C.Type (C.Struct (String.uppercase_ascii func_name ^ "_results", results)))
      else None | _ -> None) procedures_info in
  let all_record_decls, _ = List.fold_left (fun (acc, s) (_, _, sub) ->
    let _, sub_tm, _ = sub.typemap in
    let recs, s' = collect_all_records sub_tm sub s in
    (acc @ recs, s')
  ) (let r, s = collect_all_records tm gr IntSet.empty in (r, s)) procedures_info in
  let math_wrappers = [] in (* now provided by sisal_runtime.h *)

  { C.filename = filename; includes = [ "stdio.h"; "stdint.h"; "stdbool.h"; "math.h"; "iostream"; "dispatch/dispatch.h"; "Accelerate/Accelerate.h"; "sisal_runtime.h" ]; globals = math_wrappers @ all_record_decls @ result_struct_decls @ (List.map (fun p -> C.Prototype p) procedures); procedures = List.rev procedures }
