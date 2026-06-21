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

(* Per-output reduction classification: list of (returns_out_port, op, body_out_port)
   for each RETURNS output fed by a REDUCE node.  Unlike forall_fold_op (which only
   fires for a single-output fold), this enumerates EACH reduction output, so a forall
   with several `value of <reduce>` outputs (or a mix with gathers) can be lowered
   per-port.  body_out_port is the body output this REDUCE folds (via __forall_body_K). *)
let forall_reduce_ports loop_gr =
  match find_subgraph loop_gr "RETURNS" with
  | None -> []
  | Some (_, ret_gr) ->
      let pfx = "__forall_body_" in
      let plen = String.length pfx in
      let bin_to_body =
        match NM.find_opt 0 ret_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.filter_map (fun (_, _, name, bp) ->
              if String.length name > plen && String.sub name 0 plen = pfx then
                (try Some (bp, int_of_string (String.sub name plen (String.length name - plen)))
                 with _ -> None)
              else None) ins
        | _ -> [] in
      ES.fold (fun ((sn, _), (dn, dp), _) acc ->
        if dn = 0 then
          match NM.find_opt sn ret_gr.nmap with
          | Some (Simple (_, REDUCE, _, _, _)) ->
              let op =
                ES.fold (fun ((s, _), (d, p), _) a ->
                  if d = sn && p = 0 then
                    match NM.find_opt s ret_gr.nmap with
                    | Some (Literal (_, CHARACTER, v, _)) -> Some (String.lowercase_ascii v)
                    | _ -> a
                  else a) ret_gr.eset None in
              let bport =
                ES.fold (fun ((s, sp), (d, p), _) a ->
                  if d = sn && p = 1 && s = 0 then
                    (match List.assoc_opt sp bin_to_body with Some b -> Some b | None -> a)
                  else a) ret_gr.eset None in
              (match op with
               | Some o -> (dp, o, (match bport with Some b -> b | None -> 0)) :: acc
               | None -> acc)
          | _ -> acc
        else acc) ret_gr.eset []

(* Companion to forall_reduce_ports: list of (returns_out_port, body_out_port) for each
   RETURNS output fed by a DV_GATHER node (an array output).  Together they classify
   EVERY output port of a multi-output forall, so a mixed gather+reduce forall can be
   lowered per port.  The gathered value is the gather's port-1 input. *)
let forall_gather_ports loop_gr =
  match find_subgraph loop_gr "RETURNS" with
  | None -> []
  | Some (_, ret_gr) ->
      let pfx = "__forall_body_" in
      let plen = String.length pfx in
      let bin_to_body =
        match NM.find_opt 0 ret_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.filter_map (fun (_, _, name, bp) ->
              if String.length name > plen && String.sub name 0 plen = pfx then
                (try Some (bp, int_of_string (String.sub name plen (String.length name - plen)))
                 with _ -> None)
              else None) ins
        | _ -> [] in
      ES.fold (fun ((sn, _), (dn, dp), _) acc ->
        if dn = 0 then
          match NM.find_opt sn ret_gr.nmap with
          | Some (Simple (_, DV_GATHER, _, _, _)) ->
              let bport =
                ES.fold (fun ((s, sp), (d, p), _) a ->
                  if d = sn && p = 1 && s = 0 then
                    (match List.assoc_opt sp bin_to_body with Some b -> Some b | None -> a)
                  else a) ret_gr.eset None in
              (dp, (match bport with Some b -> b | None -> dp)) :: acc
          | _ -> acc
        else acc) ret_gr.eset []

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
          let is_arr = List.mem sym [DV_CREATE; DV_RESHAPE; DV_SLICE; DV_PERMUTE; DV_ROTATE; DV_COMPRESS; DV_OUTERPRODUCT; DV_SORT; DV_REVERSE; DV_RESHAPE_BY_SHAPE; DV_GATHER; AGATHER; ASCATTER; ABUILD; AFILL; ACREATE; RELEMENTS; AREPLACE; DV_RANK_REDUCE; DV_RANK_REPLACE] in
          let ty = if is_int then C.Basic "int32_t" else if is_arr then C.Basic "sisal_array_t" else C.Basic "float" in
          Array.iteri (fun i _ -> set_ty cur_gid nid i `Out ty) outs;
          if is_arr || List.mem sym [ALIML; ALIMH; ASIZE; DV_SCATTER; AELEMENT; DV_ELEMENT; DV_LOAD_LINEAR; DV_DIMENSION; DV_COMPRESS; DV_SORT; DV_REVERSE; DV_ROTATE; DV_SLICE; DV_PERMUTE; REDUCE_ALL] then
            set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
      | Compound (_, sym, _, pr, sub, _) ->
          let sub_gid = try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1 in
          let is_forall = get_compound_type pr = If1_forall in
          let fold_op = if is_forall then forall_fold_op sub else None in
          let is_fold = fold_op <> None in
          (* A multi-output forall may have REDUCTION output ports (value of sum, …).
             Don't seed port 0 as sisal_array_t when it's a reduction -- let pass2
             infer its scalar type from the REDUCE output edge (as it already does for
             the other reduction ports). *)
          let rports = if is_forall then forall_reduce_ports sub else [] in
          let port0_is_reduce = List.exists (fun (dp, _, _) -> dp = 0) rports in
          if (is_forall || sym = STREAM || sym = MAT) && not is_fold && not port0_is_reduce then
            set_ty cur_gid nid 0 `Out (C.Basic "sisal_array_t");
          (match fold_op with
           | Some ("argmax" | "argmin") -> set_ty cur_gid nid 0 `Out (C.Basic "int32_t")
           | _ -> ());
          pass1 sub sub_gid
      | _ -> ()
    ) g.nmap in

  let rec pass2 g cur_gid =
    let tm2 = get_typemap_tm g in
    let changed_edges = ES.fold (fun ((sn, sp), (dn, dp), ty_id) ch ->
      let sty = get_ty cur_gid sn sp `Out in
      let dty = get_ty cur_gid dn dp `In in
      (* Seed concrete types from edge type tags (e.g. INTEGRAL on DV_ELEMENT output edges).
         Only seed the destination when the source agrees or is still unknown — prevents
         body-expression edge tags (e.g. DOUBLE on an argmax output) from overriding a
         source that pass0/pass1 already typed as int32_t. *)
      let c0 = match TM.find_opt ty_id tm2 with
        | Some edge_if1_ty ->
            let ety = c_type_of_if1_ty tm2 edge_if1_ty in
            if ety <> C.Basic "float" then
              (let c1 = if sty = C.Basic "float" then set_ty_c cur_gid sn sp `Out ety else false in
               let c2 = if dty = C.Basic "float" && (sty = C.Basic "float" || sty = ety) then set_ty_c cur_gid dn dp `In ety else false in
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
            if List.mem sym [ALIML; ALIMH; ASIZE; AELEMENT; DV_ELEMENT; DV_RANK_REDUCE; DV_RANK_REPLACE; DV_LOAD_LINEAR; DV_DIMENSION; DV_COMPRESS; DV_SORT; DV_REVERSE; DV_ROTATE; DV_SLICE; DV_PERMUTE; REDUCE_ALL; AREPLACE]
            then let in0 = get_ty cur_gid nid 0 `In in
                 if in0 = C.Basic "float" then set_ty_c cur_gid nid 0 `In (C.Basic "sisal_array_t") else false
            else false in
          let c2 =
            if sym = AELEMENT || sym = DV_ELEMENT || sym = DV_RANK_REDUCE || sym = DV_RANK_REPLACE || sym = DV_LOAD_LINEAR || sym = DV_OFFSET_AT || sym = DV_DIMENSION || sym = AREPLACE
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
          let is_arr = List.mem sym [DV_CREATE; DV_RESHAPE; DV_SLICE; DV_PERMUTE; DV_ROTATE; DV_COMPRESS; DV_OUTERPRODUCT; DV_SORT; DV_REVERSE; DV_RESHAPE_BY_SHAPE; DV_GATHER; AGATHER; ASCATTER; ABUILD; AFILL; ACREATE; RELEMENTS; AREPLACE; DV_RANK_REDUCE; DV_RANK_REPLACE] in
          if is_arr then (
            Array.iteri (fun i _ -> set_ty cur_gid nid i `Out (C.Basic "sisal_array_t")) outs;
            set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
          );
          if List.mem sym [ALIML; ALIMH; ASIZE; DV_SCATTER; AELEMENT; DV_ELEMENT; DV_LOAD_LINEAR; DV_DIMENSION; DV_COMPRESS; DV_SORT; DV_REVERSE; DV_ROTATE; DV_SLICE; DV_PERMUTE; REDUCE_ALL] then
            set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
      | Compound (_, sym, _, pr, sub, _) ->
          let sub_gid = try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1 in
          let is_forall = get_compound_type pr = If1_forall in
          let fold_op = if is_forall then forall_fold_op sub else None in
          let is_fold = fold_op <> None in
          (* A multi-output forall may have REDUCTION output ports (value of sum, …).
             Don't seed port 0 as sisal_array_t when it's a reduction -- let pass2
             infer its scalar type from the REDUCE output edge (as it already does for
             the other reduction ports). *)
          let rports = if is_forall then forall_reduce_ports sub else [] in
          let port0_is_reduce = List.exists (fun (dp, _, _) -> dp = 0) rports in
          if (is_forall || sym = STREAM || sym = MAT) && not is_fold && not port0_is_reduce then
            set_ty cur_gid nid 0 `Out (C.Basic "sisal_array_t");
          (match fold_op with
           | Some ("argmax" | "argmin") -> set_ty cur_gid nid 0 `Out (C.Basic "int32_t")
           | _ -> ());
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
    (* Check var_map first: if a variable was already pre-declared for this port
       (e.g., by declare_outputs at an outer scope), reuse that name so the
       FORALL accumulator writes to the outer-scope variable rather than
       declaring a new inner-scope one that becomes inaccessible after the
       compound block closes. *)
    let name =
      match FullPortMap.find_opt (gid, nid, pid, dir) env.var_map with
      | Some (C.Id n) -> n
      | _ ->
          let g = get_graph_by_gid env gid in
          get_c_name env.proc_map env.gid_name_map gid nid pid dir g
    in
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
      let idx = if sym = DV_LOAD_LINEAR then e2 else C.BinOp (C.Sub, e2, C.Index (C.Member (e1, "lower_bound"), C.LitInt 0)) in
      C.Index (cast_ptr, idx)
  | RANGEGEN -> C.BinOp (C.Add, C.BinOp (C.Sub, e2, e1), C.LitInt 1)
  | ASIZE | DV_SCATTER -> C.Cast (C.Basic "int32_t", C.Member (e1, "size"))
  | ALIML -> C.Cast (C.Basic "int32_t", C.Index (C.Member (e1, "lower_bound"), C.LitInt 0))
  | ALIMH -> C.Cast (C.Basic "int32_t", C.BinOp (C.Sub, C.BinOp (C.Add, C.Index (C.Member (e1, "lower_bound"), C.LitInt 0), C.Cast (C.Basic "int64_t", C.Member (e1, "size"))), C.LitInt 1))
  | DV_NUM_RANK -> C.Member (e1, "rank")
  | DV_DIMENSION -> C.Call ("sisal_dv_dimension", [ e2; e1 ])
  | DV_CONFORM -> C.Call ("sisal_dv_conform", [ e1; e2 ])
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
  | DV_RANK_REDUCE -> C.Call ("sisal_dv_rank_reduce", [ e1; e2 ])
  | DV_RANK_REPLACE -> C.Call ("sisal_dv_replace_slice", [ e1; e2; get_in_expr 2 ])
  | DV_PERMUTE ->
      (* PERMUTE(A, d0, d1, ...) reorders axes: input port 0 = array, ports 1..rank
         = the new axis order.  Forward ALL the perm indices (variadic), with their
         count, so a rank-k permute/transpose works -- not just the first axis. *)
      let perm_ports =
        ES.fold (fun (_, (dn, dp), _) acc ->
          if dn = nid && dp >= 1 then IntSet.add dp acc else acc) gr.eset IntSet.empty
        |> IntSet.elements
      in
      let perm_args = List.map (fun p -> get_in_expr p) perm_ports in
      C.Call ("sisal_array_permute",
        e1 :: C.LitInt (List.length perm_args) :: perm_args)
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
  | FINALVALUE -> e1
  | sym -> failwith (Printf.sprintf "Unsupported IF1 Simple node symbol at gid=%d nid=%d: %s" gid nid (string_of_node_sym sym)) in
  (* For an INVOCATION of a multi-RETURN function, unpack the returned struct.
     Gate on the CALLEE's declared arity (does it return a *_results record?),
     NOT on the count of live output edges: a dead/unused output would otherwise
     drop the live count to 1 and route a record-returning call through the
     single-value cast path (casting the whole record -> type error / dropped out). *)
  let stmts, e' = match sym with
    | INVOCATION ->
        let out_ports = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
        let callee_name = match rhs with C.Call (fn, _) -> Some fn | _ -> None in
        let callee_arity = match callee_name with
          | Some fn ->
              IntMap.fold (fun pnid pname acc ->
                if pname = fn then
                  (match IntMap.find_opt pnid env.procedures_info with
                   | Some sub ->
                       ES.fold (fun (_, (dn, dp), ty) a ->
                         if dn = 0 && not (is_error_port ty sub) then IntSet.add dp a else a)
                         sub.eset IntSet.empty |> IntSet.cardinal
                   | None -> acc)
                else acc) env.proc_map 0
          | None -> 0 in
        if callee_arity > 1 then begin
          let struct_name = match callee_name with
            | Some fn -> Printf.sprintf "%s_results" (String.uppercase_ascii fn)
            | None -> "UNKNOWN_results" in
          let tmp = Printf.sprintf "_mr_%s_%d" (scope_of env.gid_name_map gid) nid in
          let decl_tmp = C.Decl (C.Basic ("struct " ^ struct_name), tmp, Some rhs) in
          (* extract .res_<port> for each LIVE output port (dead ones bind nothing) *)
          List.fold_left (fun (acc, e) port ->
            let field = C.Member (C.Id tmp, Printf.sprintf "res_%d" port) in
            let ss, e' = assign_with_cast e gid nid port `Out field in
            (acc @ ss, e'))
          ([decl_tmp], env) out_ports
        end else
          assign_with_cast env gid nid 0 `Out rhs
    | _ -> assign_with_cast env gid nid 0 `Out rhs
  in
  ( stmts, e' )

and lower_if_graph env parent_gr nid loop_gr loop_gid =
  let gid = env.curr_gid in
  let env_loop_base = { env with parent_env = Some env; compound_nid_in_parent = nid; curr_gid = loop_gid; curr_gr = loop_gr } in
  let env_loop_base = scan_fanout loop_gr loop_gid env_loop_base in
  let node = match NM.find_opt nid parent_gr.nmap with Some n -> n | _ -> failwith "no node" in
  let decl_stmts, env_loop_base = declare_outputs env_loop_base parent_gr gid nid node in
  (* The IF compound's output ports -- every branch assigns into these (declared
     once by declare_outputs above, so the if/else blocks just assign). *)
  let if_out_pids = ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc) parent_gr.eset IntSet.empty |> IntSet.elements in
  (* Assign a branch graph's boundary outputs to the IF compound's outputs. *)
  let assign_if_outs e br_gr br_gid =
    List.fold_left (fun (acc, e) dp ->
      let src_opt = match FullPortMap.find_opt (br_gid, 0, dp, `In) e.var_map with
        | Some _ as found -> found
        | None ->
            (match ES.fold (fun (src, dst, _) a -> if dst = (0, dp) then Some src else a) br_gr.eset None with
             | Some (sn, sp) -> FullPortMap.find_opt (br_gid, sn, sp, `Out) e.var_map
             | None -> None) in
      match src_opt with
      | Some src_expr -> let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in (acc @ stmts, e')
      | None -> (acc, e))
      ([], { e with curr_gid = gid; curr_gr = parent_gr }) if_out_pids
  in
  (* Recursively lower an if-structured graph `g` (the IF compound's graph, or a
     THEN/ELSE arm's graph).  If it has a PREDICATE it IS an if -> emit `if/else`
     and recurse into THEN and ELSE (an `elseif` chain nests deeper here).  If it
     has no PREDICATE it is a plain value branch -> lower straight-line and assign
     its result to the IF outputs (the base case / chain terminator). *)
  let rec lower_chain e pg comp_nid g ggid =
    match find_subgraph g "PREDICATE" with
    | None ->
        let stmts, e = lower_graph e pg comp_nid g ggid in
        let assigns, e = assign_if_outs e g ggid in
        (stmts @ assigns, e)
    | Some (pred_cid, pred_sg) ->
        (* copy in THIS arm's boundary inputs from its parent (the base case gets
           this free via lower_graph; the nested-if case must do it explicitly so
           the inner PREDICATE/THEN/ELSE can read I/E/...). *)
        let in_stmts, e = init_boundary_ports e pg comp_nid g ggid in
        let pgid = try GidMap.find (ggid, pred_cid) e.gid_table with _ -> -1 in
        let env_pred = { e with parent_env = Some e; curr_gid = pgid; curr_gr = pred_sg; parent_map = IntMap.add pgid (ggid, pred_cid) e.parent_map } in
        let pred_stmts, e_pred = lower_graph env_pred g pred_cid pred_sg pgid in
        let v_pred = match ES.fold (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc) pred_sg.eset None with
          | Some (sn, sp) -> get_expr e_pred pgid sn sp `Out
          | None -> C.LitInt 0 in
        let e = { e with var_map = e_pred.var_map; type_table = e_pred.type_table; seen_decls = e_pred.seen_decls } in
        (* lower_chain returns env with curr_gid reset to the outer `gid`; restore
           the current if-level (`ggid`/`g`) before each branch so its boundary
           copy-in resolves against THIS scope, not the outer one. *)
        let at_level e = { e with curr_gid = ggid; curr_gr = g } in
        let then_cid, then_sg = match find_subgraph g "THEN" with | Some x -> x | _ -> failwith "no THEN" in
        let tgid = try GidMap.find (ggid, then_cid) e.gid_table with _ -> -1 in
        let e = at_level e in
        let then_stmts, e =
          lower_chain { e with parent_env = Some e; curr_gid = tgid; curr_gr = then_sg; parent_map = IntMap.add tgid (ggid, then_cid) e.parent_map } g then_cid then_sg tgid in
        let else_cid, else_sg = match find_subgraph g "ELSE" with | Some x -> x | _ -> failwith "no ELSE" in
        let egid = try GidMap.find (ggid, else_cid) e.gid_table with _ -> -1 in
        let e = at_level e in
        let else_stmts, e =
          lower_chain { e with parent_env = Some e; curr_gid = egid; curr_gr = else_sg; parent_map = IntMap.add egid (ggid, else_cid) e.parent_map } g else_cid else_sg egid in
        (in_stmts @ [ C.Compound (pred_stmts @ [ C.If (v_pred, then_stmts, else_stmts) ]) ],
         { e with curr_gid = gid; curr_gr = parent_gr })
  in
  let body, e_final = lower_chain env_loop_base parent_gr nid loop_gr loop_gid in
  (decl_stmts @ body, { e_final with curr_gid = gid; curr_gr = parent_gr })

and lower_forall env gr gid nid loop_gr sub_gid pr =
  (* ===== FRESH forall -> C lowering (rebuilt from scratch) =====
     Step 1: locate the GENERATOR / BODY / RETURNS subgraph nodes inside loop_gr
     via a node-map walk.  (NM-walk is fine HERE -- we are only FINDING the three
     structural children of the forall, not lowering anything yet.)  Everything
     else is built up step by step.  The previous (recursive zip_loops) version is
     preserved below as `_lower_forall_recursive_OLD`. *)
  let _ = (nid, sub_gid, pr) in
  let find_role role =
    NM.fold
      (fun n node acc ->
        match acc with
        | Some _ -> acc
        | None -> (
            match node with
            | Compound (_, _, _, prag, sub, _) when get_compound_type prag = role ->
                Some (n, sub)
            | _ -> None))
      loop_gr.nmap None
  in
  let _generator = find_role If1_generator in
  let _body = find_role If1_body in
  let _returns = find_role If1_results in

  (* Step 2: RECURSIVE LOCAL-SYMTAB VISITOR.  Declare, in THIS forall scope, one C
     declarator per local-symtab entry -- not just the forall's own symtab but,
     recursively, the GENERATOR / BODY / RETURNS subgraphs (and anything nested in
     them).  Each subgraph has its own GID (its C-name scope) so distinct
     declarations never collide.  All land as BARE decls here, ready to be filled
     when their producing node is lowered by the (upcoming) topo edge walk.  The
     ONLY entries we can fully initialise now are the forall-level boundary imports
     (val_def = 0) -- their value already exists in the outer scope.  Type comes
     from each entry's `val_ty` via the subgraph's own typemap. *)
  let env_loop =
    { env with parent_env = Some env; compound_nid_in_parent = nid;
      curr_gid = sub_gid; curr_gr = loop_gr }
  in
  let _ = env_loop in
  (* outer value feeding the forall compound's input port k (boundary imports) *)
  let parent_feed k =
    match
      ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = nid && dp = k then Some (sn, sp) else acc) gr.eset None
    with
    | Some (sn, sp) -> Some (get_expr env gid sn sp `Out)
    | None -> None
  in
  (* The anticipatory list, as a binding tracker: every declared slot is recorded
     in var_map keyed by (gid, val_def, def_port, `Out) so later lowering can
     RESOLVE a port to its slot name -- or OVERRIDE it (relays). *)
  let rec collect g ggid (acc, seen, e) =
    let tm = get_typemap_tm g in
    let cty_of v = try c_type_of_if1_ty tm (TM.find v.val_ty tm) with _ -> C.Basic "float" in
    let cs, _ = g.symtab in
    let acc, seen, e =
      SM.fold
        (fun _ v (acc, seen, e) ->
          let cname =
            get_c_name e.proc_map e.gid_name_map ggid v.val_def v.def_port `Out g
          in
          if StringSet.mem cname seen then (acc, seen, e)
          else
            let init =
              if ggid = sub_gid && v.val_def = 0 then parent_feed v.def_port else None
            in
            let e =
              { e with var_map =
                  FullPortMap.add (ggid, v.val_def, v.def_port, `Out) (C.Id cname) e.var_map }
            in
            (acc @ [ C.Decl (cty_of v, cname, init) ], StringSet.add cname seen, e))
        cs (acc, seen, e)
    in
    NM.fold
      (fun cn node st ->
        match node with
        | Compound (_, _, _, _, sub, _) ->
            let cgid = try GidMap.find (ggid, cn) e.gid_table with _ -> -1 in
            collect sub cgid st
        | _ -> st)
      g.nmap (acc, seen, e)
  in
  let sym_decls, seen2, env_loop = collect loop_gr sub_gid ([], StringSet.empty, env_loop) in
  (* Mark the hoisted names as already-declared so later lowering (lower_graph for
     the body/returns) ASSIGNS them instead of re-declaring. *)
  let env_loop =
    { env_loop with seen_decls = StringSet.union env_loop.seen_decls seen2 }
  in

  (* Step 3: BOUNDARY COPY-IN (uniform).  A subgraph boundary INPUT is fed from its
     parent.  Treat EVERY boundary crossing the same way the forall treats its own
     inputs: declare the slot (step 2) + ASSIGN it from the parent on entry --
     `v_GEN_…_N = v_FORALL_…_N;`.  So consumers read the subgraph's own (now live)
     name; no var_map override, no dead relay decls.  Recurses through nested
     GENERATORs (cross): the inner copy-in reads the outer's slot, already assigned.
     These are loop-invariant, so they sit BEFORE the loops. *)
  let gen_gid_of pg gnid = try GidMap.find (pg, gnid) env.gid_table with _ -> -1 in
  let rec relay_copyins parent_g parent_nid parent_gid g ggid =
    let in_ports =
      ES.fold (fun ((sn, sp), _, _) acc -> if sn = 0 then IntSet.add sp acc else acc)
        g.eset IntSet.empty
    in
    let here =
      IntSet.fold
        (fun k acc ->
          match
            ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
              if dn = parent_nid && dp = k then Some (sn, sp) else acc) parent_g.eset None
          with
          | Some (sn, sp) ->
              let parent_expr = get_expr env_loop parent_gid sn sp `Out in
              let dst = get_c_name env.proc_map env.gid_name_map ggid 0 k `Out g in
              acc @ [ C.Expr (C.BinOp (C.Assign, C.Id dst, parent_expr)) ]
          | None -> acc)
        in_ports []
    in
    let nested =
      match find_subgraph g "GENERATOR" with
      | Some (ign, igr) -> relay_copyins g ign ggid igr (gen_gid_of ggid ign)
      | None -> []
    in
    here @ nested
  in
  let relay_stmts =
    match _generator with
    | None -> []
    | Some (gen_nid, gen_gr) ->
        relay_copyins loop_gr gen_nid sub_gid gen_gr (gen_gid_of sub_gid gen_nid)
  in

  (* Step 4: GENERATOR -> nested C loops.  `lower_gen g ggid inner` builds this
     generator level's loop(s) wrapping `inner`, recursing for a nested GENERATOR
     (cross).  Per level: materialise dataflow (bound math) via lower_node; the axis
     nodes become the loop -- RANGEGEN -> counted for; DV_SCATTER/ARRAY_SCATTER ->
     element loop (element type FROM THE IF1 typemap, not hardcoded); several axes
     at one level = a dot (one counter, siblings in lockstep); ARRAY_SCATTER's
     port 1 is the `at`-index (= lower_bound + k). *)
  let rec lower_gen ?(before = []) g ggid inner =
    let env_g0 = { env_loop with curr_gid = ggid; curr_gr = g } in
    let slot n p = get_c_name env.proc_map env.gid_name_map ggid n p `Out g in
    let tm = get_typemap_tm g in
    let port_cty n p =
      match
        ES.fold (fun ((sn, sp), _, t) acc -> if sn = n && sp = p && t <> 0 then Some t else acc)
          g.eset None
      with
      | Some t -> (try c_type_of_if1_ty tm (TM.find t tm) with _ -> C.Basic "int32_t")
      | None -> C.Basic "int32_t"
    in
    let bind e n p =
      { e with var_map = FullPortMap.add (ggid, n, p, `Out) (C.Id (slot n p)) e.var_map }
    in
    (* pass 1: materialise dataflow, collect axis node ids *)
    let pre, ranges, scatters, env_g =
      List.fold_left
        (fun (pre, rs, ss, e) n ->
          match NM.find_opt n g.nmap with
          | Some (Literal _) | Some (Compound _) -> (pre, rs, ss, e)
          | Some (Simple (_, RANGEGEN, _, _, _)) ->
              (pre, rs @ [ n ], ss, bind (bind (bind e n 0) n 1) n 2)
          | Some (Simple (_, DV_SCATTER, _, _, _)) ->
              (pre, rs, ss @ [ (n, `Dv) ], bind e n 0)
          | Some (Simple (_, ASCATTER, _, _, _)) ->
              (pre, rs, ss @ [ (n, `Arr) ], bind (bind e n 0) n 1)
          | Some (Simple _) ->
              (* dataflow (bound math) is materialised UP FRONT by materialize_bounds
                 (loop-invariant, hoisted before the alloc), so skip it here. *)
              (pre, rs, ss, e)
          | _ -> (pre, rs, ss, e))
        ([], [], [], env_g0) (topo_sort g)
    in
    let resolve_in n p =
      match
        ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
          if dn = n && dp = p then Some (sn, sp) else acc) g.eset None
      with
      | Some (sn, sp) -> get_expr env_g ggid sn sp `Out
      | None -> C.LitInt 0
    in
    (* recurse into a nested GENERATOR (cross) for the inner body *)
    let inner' =
      match find_subgraph g "GENERATOR" with
      | Some (ign, igr) -> lower_gen igr (gen_gid_of ggid ign) inner
      | None -> inner
    in
    match (ranges, scatters) with
    | prim :: sibs, [] ->
        let it = slot prim 0 in
        let lb = resolve_in prim 0 and ub = resolve_in prim 1 in
        (* Each RANGEGEN re-exports lb/ub on ports 1/2; the RETURNS reads them for
           the extent (ub-lb+1).  Materialise those output slots (loop-invariant,
           before the loop) so they are live. *)
        let bound_outs =
          List.concat_map
            (fun ax ->
              [ C.Expr (C.BinOp (C.Assign, C.Id (slot ax 1), resolve_in ax 0));
                C.Expr (C.BinOp (C.Assign, C.Id (slot ax 2), resolve_in ax 1)) ])
            (prim :: sibs)
        in
        (* dot siblings advance in lockstep: sib = sib_lb + (primary - primary_lb) *)
        let sib_decls =
          List.map
            (fun s ->
              C.Expr (C.BinOp (C.Assign, C.Id (slot s 0),
                C.BinOp (C.Add, resolve_in s 0,
                  C.BinOp (C.Sub, C.Id it, lb)))))
            sibs
        in
        pre @ bound_outs @ before
        @ [ C.For
              ( C.Expr (C.BinOp (C.Assign, C.Id it, lb)),
                C.BinOp (C.Le, C.Id it, ub),
                C.UnaryOp (C.PostInc, C.Id it),
                sib_decls @ inner' ) ]
    | [], (pn, _) :: _ ->
        (* element scatter (dot of scatters share one counter k over the array) *)
        let k = Printf.sprintf "__k_%d" ggid in
        let parr = resolve_in pn 0 in
        let assigns =
          List.concat_map
            (fun (s, kind) ->
              let arr = resolve_in s 0 in
              let ety = port_cty s 0 in
              let elem =
                C.Index (C.Cast (C.Pointer (ety, []), C.Member (arr, "data")), C.Id k)
              in
              let base = [ C.Expr (C.BinOp (C.Assign, C.Id (slot s 0), elem)) ] in
              (* the `at` index (port 1) only exists for ARRAY_SCATTER, and only when
                 it is actually consumed (`for a in A at i`); skip it otherwise. *)
              let at_used =
                ES.exists (fun ((sn, sp), _, _) -> sn = s && sp = 1) g.eset
              in
              match kind with
              | `Arr when at_used ->
                  (* `at` index (port 1) = lower_bound[0] + k *)
                  let idx =
                    C.BinOp (C.Add,
                      C.Cast (C.Basic "int32_t", C.Index (C.Member (arr, "lower_bound"), C.LitInt 0)),
                      C.Id k)
                  in
                  base @ [ C.Expr (C.BinOp (C.Assign, C.Id (slot s 1), idx)) ]
              | _ -> base)
            scatters
        in
        pre @ before
        @ [ C.For
              ( C.Decl (C.Basic "int32_t", k, Some (C.LitInt 0)),
                C.BinOp (C.Lt, C.Id k, C.Cast (C.Basic "int32_t", C.Member (parr, "size"))),
                C.UnaryOp (C.PostInc, C.Id k),
                assigns @ inner' ) ]
    | [], [] -> pre @ before @ inner'
    | _ :: _, _ :: _ -> pre @ inner' (* mixed range+scatter at one level: unsupported *)
  in
  (* Step 5: BODY + RETURNS (gather).  Single-axis ARRAY gather for now:
     - bind the generator compound's outputs to its internal producers, so the
       body's boundary copy-in (via lower_graph) resolves the iterator/lb/ub;
     - lower the BODY graph -> body_stmts (incl. its per-iteration copy-ins +
       anonymous compute, all inside the loop) and body_res (the value to store);
     - alloc the result once before the loop (count from the primary axis extent);
     - store body_res at a running gather counter inside the loop. *)
  let loop_stmts, out_decls, out_binds =
    match _generator with
    | None -> ([], [], [])
    | Some (gen_nid, gen_gr) ->
        let gen_gid = gen_gid_of sub_gid gen_nid in
        let env_gen_view = { env_loop with curr_gid = gen_gid; curr_gr = gen_gr } in
        let gen_internal n p =
          ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = n && dp = p then Some (sn, sp) else acc) gen_gr.eset None
        in
        ignore (env_gen_view, gen_internal);
        (* (a) generator compound OUTPUT propagation, recursively.  A generator
           compound's output port re-exports an internal value (its iterator, lb/ub,
           or -- for cross -- a NESTED generator's output).  Bind the parent-scope
           view `(parent_gid, comp_nid, port)` to the internal producer's value, so
           the BODY/RETURNS resolve I/J straight to the (in-scope) loop variables.
           Recurse innermost-first so an outer port that re-exports a nested output
           resolves through the nested binding. *)
        let rec bind_gen_outputs parent_gid comp_nid g ggid e =
          let e =
            match find_subgraph g "GENERATOR" with
            | Some (ign, igr) -> bind_gen_outputs ggid ign igr (gen_gid_of ggid ign) e
            | None -> e
          in
          let out_ports =
            ES.fold (fun (_, (dn, dp), _) acc -> if dn = 0 then IntSet.add dp acc else acc)
              g.eset IntSet.empty
          in
          IntSet.fold
            (fun p e ->
              match
                ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
                  if dn = 0 && dp = p then Some (sn, sp) else acc) g.eset None
              with
              | Some (sn, sp) ->
                  let v = get_expr { e with curr_gid = ggid; curr_gr = g } ggid sn sp `Out in
                  { e with var_map = FullPortMap.add (parent_gid, comp_nid, p, `Out) v e.var_map }
              | None -> e)
            out_ports e
        in
        let env_loop = bind_gen_outputs sub_gid gen_nid gen_gr gen_gid env_loop in
        (* (a2) materialise ALL generator-nest bound math (n-1, m-1, ...) UP FRONT.
           It is loop-invariant, so hoisting it before the alloc lets the result
           extent reference it even for nested expression bounds in a cross. *)
        let rec materialize_bounds g ggid e =
          let e = { e with curr_gid = ggid; curr_gr = g } in
          let stmts, e =
            List.fold_left
              (fun (acc, e) n ->
                match NM.find_opt n g.nmap with
                | Some (Simple (_, (RANGEGEN | DV_SCATTER | ASCATTER), _, _, _)) -> (acc, e)
                | Some (Simple _ as node) ->
                    let s, e' = lower_node e g n node in (acc @ s, e')
                | _ -> (acc, e))
              ([], e) (topo_sort g)
          in
          match find_subgraph g "GENERATOR" with
          | Some (ign, igr) ->
              let s2, e = materialize_bounds igr (gen_gid_of ggid ign) e in
              (stmts @ s2, e)
          | None -> (stmts, e)
        in
        let bound_stmts, env_loop = materialize_bounds gen_gr gen_gid env_loop in
        let env_loop = { env_loop with curr_gid = sub_gid; curr_gr = loop_gr } in
        (* (b) lower the BODY -> body_stmts + ALL outputs (one per return clause),
           sorted by destination port (forall output port = body output port). *)
        let body_stmts, body_outs =
          match find_subgraph loop_gr "BODY" with
          | Some (body_nid, body_gr) ->
              let body_gid = gen_gid_of sub_gid body_nid in
              let env_body =
                { env_loop with parent_env = Some env_loop; curr_gid = body_gid;
                  curr_gr = body_gr;
                  parent_map = IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map }
              in
              let bstmts, e_body = lower_graph env_body loop_gr body_nid body_gr body_gid in
              let outs =
                ES.fold (fun ((sn, sp), (dn, dp), t) acc ->
                  if dn = 0 then (dp, get_expr e_body body_gid sn sp `Out, t) :: acc else acc)
                  body_gr.eset []
                |> List.sort (fun (a, _, _) (b, _, _) -> compare a b)
              in
              (bstmts, outs)
          | None -> ([], [])
        in
        let tm = get_typemap_tm loop_gr in
        (* per-dimension extents (shared by all GATHER outputs) *)
        let rec collect_extents g ggid =
          let view = { env_loop with curr_gid = ggid; curr_gr = g } in
          let resolve n p =
            match
              ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
                if dn = n && dp = p then Some (sn, sp) else acc) g.eset None
            with
            | Some (sn, sp) -> get_expr view ggid sn sp `Out
            | None -> C.LitInt 0
          in
          let here =
            match
              List.find_opt (fun n ->
                match NM.find_opt n g.nmap with
                | Some (Simple (_, (RANGEGEN | DV_SCATTER | ASCATTER), _, _, _)) -> true
                | _ -> false) (topo_sort g)
            with
            | Some n -> (
                match NM.find_opt n g.nmap with
                | Some (Simple (_, RANGEGEN, _, _, _)) ->
                    let lb = resolve n 0 and ub = resolve n 1 in
                    [ (C.BinOp (C.Add, C.BinOp (C.Sub, ub, lb), C.LitInt 1), lb) ]
                | _ ->
                    [ (C.Cast (C.Basic "int32_t", C.Member (resolve n 0, "size")), C.LitInt 1) ])
            | None -> []
          in
          let rest =
            match find_subgraph g "GENERATOR" with
            | Some (ign, igr) -> collect_extents igr (gen_gid_of ggid ign)
            | None -> []
          in
          here @ rest
        in
        let extents = collect_extents gen_gr gen_gid in
        let rank = max 1 (List.length extents) in
        let count =
          List.fold_left (fun acc (e, _) -> C.BinOp (C.Mul, acc, e)) (C.LitInt 1) extents
        in
        let gctr = Printf.sprintf "__g_%d" sub_gid in
        (* which forall output ports are REDUCTIONS (vs gathers) *)
        let reduce_specs = forall_reduce_ports loop_gr in
        let reduce_op_of p =
          List.find_map (fun (op_port, opn, _) -> if op_port = p then Some opn else None)
            reduce_specs
        in
        (* primary axis iterator (the Sisal index, for argmax/argmin) *)
        let primary_iter =
          match
            List.find_opt (fun n ->
              match NM.find_opt n gen_gr.nmap with
              | Some (Simple (_, RANGEGEN, _, _, _)) -> true | _ -> false)
              (topo_sort gen_gr)
          with
          | Some n -> Some (C.Id (get_c_name env.proc_map env.gid_name_map gen_gid n 0 `Out gen_gr))
          | None -> None
        in
        (* (c) per forall OUTPUT PORT: a gather (alloc + store) or a reduction
           (init + accumulate).  All share one loop + one gather counter. *)
        let per =
          List.map
            (fun (port, value, tid) ->
              let res_name = get_c_name env.proc_map env.gid_name_map gid nid port `Out gr in
              let res_v = C.Id res_name in
              let out_ty = try c_type_of_if1_ty tm (TM.find tid tm) with _ -> C.Basic "int32_t" in
              let cast = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type out_ty); value ]) in
              match reduce_op_of port with
              | Some ("argmax" | "argmin" as op) ->
                  (* argmax/argmin: track the best VALUE in a temp accumulator and
                     return the Sisal INDEX (the loop iterator) of the extremum.
                     Result type is the index (int32), accumulator is the value. *)
                  let inf =
                    match out_ty with
                    | C.Basic "double" -> C.Id "1e308"
                    | C.Basic "float" -> C.Id "3.4028235e+38f"
                    | _ -> C.Id "0x7fffffff"
                  in
                  let accn = Printf.sprintf "__argm_%d_%d" sub_gid port in
                  let accv = C.Id accn in
                  let sentinel = if op = "argmax" then C.UnaryOp (C.Negate, inf) else inf in
                  let cmp = if op = "argmax" then C.Gt else C.Lt in
                  let idx = match primary_iter with Some i -> i | None -> C.LitInt 0 in
                  let before =
                    [ C.Decl (out_ty, accn, Some sentinel);
                      C.Expr (C.BinOp (C.Assign, res_v, C.LitInt 0)) ]
                  in
                  let update =
                    C.If (C.BinOp (cmp, cast, accv),
                      [ C.Expr (C.BinOp (C.Assign, accv, cast));
                        C.Expr (C.BinOp (C.Assign, res_v, idx)) ], [])
                  in
                  (before, [ update ], [], (res_name, C.Basic "int32_t"), (port, res_v))
              | Some op ->
                  let inf =
                    match out_ty with
                    | C.Basic "double" -> C.Id "1e308"
                    | C.Basic "float" -> C.Id "3.4028235e+38f"
                    | _ -> C.Id "0x7fffffff"
                  in
                  let init_val =
                    match op with
                    | "product" -> C.LitInt 1 | "least" -> inf
                    | "greatest" -> C.UnaryOp (C.Negate, inf) | _ -> C.LitInt 0
                  in
                  let update =
                    match op with
                    | "product" -> C.Expr (C.BinOp (C.Assign, res_v, C.BinOp (C.Mul, res_v, cast)))
                    | "least" -> C.If (C.BinOp (C.Lt, cast, res_v), [ C.Expr (C.BinOp (C.Assign, res_v, cast)) ], [])
                    | "greatest" -> C.If (C.BinOp (C.Gt, cast, res_v), [ C.Expr (C.BinOp (C.Assign, res_v, cast)) ], [])
                    | _ ->
                        let o = if out_ty = C.Basic "bool" then C.LogOr else C.Add in
                        C.Expr (C.BinOp (C.Assign, res_v, C.BinOp (o, res_v, cast)))
                  in
                  ( [ C.Expr (C.BinOp (C.Assign, res_v, init_val)) ], [ update ], [],
                    (res_name, out_ty), (port, res_v) )
              | None ->
                  let alloc =
                    C.Expr (C.BinOp (C.Assign, res_v,
                      C.Call ("sisal_array_alloc_empty",
                        [ C.LitInt rank; C.LitInt tid; C.Cast (C.Basic "uint64_t", count) ])))
                    :: List.concat
                         (List.mapi (fun k (e, lb) ->
                            [ C.Expr (C.BinOp (C.Assign, C.Index (C.Member (res_v, "dims"), C.LitInt k), e));
                              C.Expr (C.BinOp (C.Assign, C.Index (C.Member (res_v, "lower_bound"), C.LitInt k), lb)) ])
                            extents)
                  in
                  let store =
                    [ C.Expr (C.BinOp (C.Assign,
                        C.Index (C.Cast (C.Pointer (out_ty, []), C.Member (res_v, "data")), C.Id gctr),
                        cast)) ]
                  in
                  (* BOX-then-FLATTEN: when the gathered body value is itself an array
                     (out_ty = sisal_array_t), the loop boxed row DESCRIPTORS into
                     res_v (rank = outer axes).  After the loop, re-pack into a flat
                     rank-(outer + elem.rank) array_dv: read the element shape ONCE off
                     the first boxed row (rectangular), memcpy each row's bytes. *)
                  let sat = C.Basic "sisal_array_t" in
                  let after =
                    if out_ty <> sat then []
                    else
                      let e0 = C.Id ("__e0_" ^ res_name) and fl = C.Id ("__flat_" ^ res_name) in
                      let esz = C.Call ("sisal_elem_size", [ C.Member (e0, "type_id") ]) in
                      let ecount = C.Member (e0, "size") in
                      let bytes = C.BinOp (C.Mul, ecount, esz) in
                      let boxed i = C.Index (C.Cast (C.Pointer (sat, []), C.Member (res_v, "data")), i) in
                      let decl_e0 = C.Decl (sat, "__e0_" ^ res_name, Some (boxed (C.LitInt 0))) in
                      let decl_fl =
                        C.Decl (sat, "__flat_" ^ res_name,
                          Some (C.Call ("sisal_array_alloc_empty",
                            [ C.BinOp (C.Add, C.LitInt rank, C.Member (e0, "rank"));
                              C.Member (e0, "type_id");
                              C.Cast (C.Basic "uint64_t",
                                C.BinOp (C.Mul, C.Cast (C.Basic "uint64_t", count), ecount)) ])))
                      in
                      let outer_dims =
                        List.concat (List.mapi (fun k (e, lb) ->
                          [ C.Expr (C.BinOp (C.Assign, C.Index (C.Member (fl, "dims"), C.LitInt k), e));
                            C.Expr (C.BinOp (C.Assign, C.Index (C.Member (fl, "lower_bound"), C.LitInt k), lb)) ])
                          extents)
                      in
                      let kk = "__fk_" ^ res_name in
                      let inner_dims =
                        C.For (C.Decl (C.Basic "int32_t", kk, Some (C.LitInt 0)),
                          C.BinOp (C.Lt, C.Id kk, C.Member (e0, "rank")),
                          C.UnaryOp (C.PostInc, C.Id kk),
                          [ C.Expr (C.BinOp (C.Assign,
                              C.Index (C.Member (fl, "dims"), C.BinOp (C.Add, C.LitInt rank, C.Id kk)),
                              C.Index (C.Member (e0, "dims"), C.Id kk)));
                            C.Expr (C.BinOp (C.Assign,
                              C.Index (C.Member (fl, "lower_bound"), C.BinOp (C.Add, C.LitInt rank, C.Id kk)),
                              C.Index (C.Member (e0, "lower_bound"), C.Id kk))) ])
                      in
                      let ii = "__fi_" ^ res_name in
                      let copy =
                        C.For (C.Decl (C.Basic "int32_t", ii, Some (C.LitInt 0)),
                          C.BinOp (C.Lt, C.Id ii, C.Cast (C.Basic "int32_t", count)),
                          C.UnaryOp (C.PostInc, C.Id ii),
                          [ C.Expr (C.Call ("memcpy",
                              [ C.BinOp (C.Add,
                                  C.Cast (C.Pointer (C.Basic "char", []), C.Member (fl, "data")),
                                  C.BinOp (C.Mul, C.Cast (C.Basic "uint64_t", C.Id ii), bytes));
                                C.Member (boxed (C.Id ii), "data");
                                bytes ])) ])
                      in
                      [ decl_e0; decl_fl ] @ outer_dims @ [ inner_dims; copy;
                        C.Expr (C.BinOp (C.Assign, res_v, fl)) ]
                  in
                  (alloc, store, after, (res_name, sat), (port, res_v)))
            body_outs
        in
        let befores = List.concat_map (fun (b, _, _, _, _) -> b) per in
        let inners = List.concat_map (fun (_, i, _, _, _) -> i) per in
        let afters = List.concat_map (fun (_, _, a, _, _) -> a) per in
        let decls = List.map (fun (_, _, _, d, _) -> d) per in
        let binds = List.map (fun (_, _, _, _, b) -> b) per in
        let any_gather = List.exists (fun (p, _, _) -> reduce_op_of p = None) body_outs in
        let before = befores @ (if any_gather then [ C.Decl (C.Basic "int32_t", gctr, Some (C.LitInt 0)) ] else []) in
        let inner = body_stmts @ inners @ (if any_gather then [ C.Expr (C.UnaryOp (C.PostInc, C.Id gctr)) ] else []) in
        (bound_stmts @ lower_gen ~before gen_gr gen_gid inner @ afters, decls, binds)
  in
  (* Declare each forall output in the PARENT scope (gather -> sisal_array_t,
     reduction -> scalar), and bind it in var_map so the caller resolves it. *)
  let res_decls =
    List.filter_map
      (fun (n, t) ->
        if StringSet.mem n env.seen_decls then None
        else
          let iv = if t = C.Basic "sisal_array_t" then C.Id "{0}" else C.LitInt 0 in
          Some (C.Decl (t, n, Some iv)))
      out_decls
  in
  let env_out =
    List.fold_left
      (fun e (port, res_v) ->
        { e with var_map = FullPortMap.add (gid, nid, port, `Out) res_v e.var_map })
      { env with curr_gid = gid; curr_gr = gr;
        seen_decls =
          List.fold_left (fun s (n, _) -> StringSet.add n s) env.seen_decls out_decls }
      out_binds
  in
  (res_decls @ [ C.Compound (sym_decls @ relay_stmts @ loop_stmts) ], env_out)

and _lower_forall_recursive_OLD env gr gid nid loop_gr sub_gid pr =
  (* WIP: rewriting forall -> C for the recursive generator / returns form.
     Goal: walk the nested GENERATOR{ ... GENERATOR{ ... } } into a rank-k loop
     nest, then the nested RETURNS{ GATHER, RETURNS{ ... } } into the multi-dim
     store (linear index for array_dv, nested alloc for array).  Build it up
     starting with the generators.  The previous single-flat-loop implementation
     is kept commented just below as reference. *)
  let _ = (gid, pr) in
  (* STEP 1-3: emit the loop-nest from the generator chain --
     `for (int <ivar> = <lb>; <ivar> <= <ub>; <ivar>++) { ... }` recursively
     (innermost generator = base case, empty body).  The body comes next. *)
  (* Forall scope, with its boundary inputs (N, M, ...) wired so the generators'
     ub expressions resolve. *)
  let env_loop =
    { env with parent_env = Some env; compound_nid_in_parent = nid;
      curr_gid = sub_gid; curr_gr = loop_gr }
  in
  let env_loop = scan_fanout loop_gr sub_gid env_loop in
  let node = match NM.find_opt nid gr.nmap with Some n -> n | _ -> failwith "forall: no node" in
  let decl_stmts, env_loop = declare_outputs env_loop gr gid nid node in
  let loop_in_stmts, env_loop = init_boundary_ports env_loop gr nid loop_gr sub_gid in
  (* One IF1 value can fan out to several symbol names (e.g. a for-initial INIT carry
     where the forall result is bound to BOTH `PIVR` and `OLD PIVR` at this node/port).
     The store below writes only the canonical name (get_c_name); drive every other
     name bound to the same port from it -- one value, many registers -- so consumers
     reading any of those names (the MERGE seeds) see the value, not an empty {0}. *)
  let fanout_stmts =
    let cs, _ = gr.symtab in
    let out_ports =
      ES.fold (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc)
        gr.eset IntSet.empty in
    IntSet.fold (fun pid acc ->
      let canon = get_c_name env.proc_map env.gid_name_map gid nid pid `Out gr in
      SM.fold (fun _ v a ->
        if v.val_def = nid && v.def_port = pid then
          let nm = Printf.sprintf "v_%s_n__%d_%s"
            (scope_of env.gid_name_map gid) nid (sanitize v.val_name) in
          if nm = canon then a
          else C.Expr (C.BinOp (C.Assign, C.Id nm, C.Id canon)) :: a
        else a) cs acc)
      out_ports [] in
  match find_subgraph loop_gr "GENERATOR" with
  | Some (gen_nid, gen_gr) ->
      (* Bind each loop var's generator-compound output port to the C loop var we
         declare, so the body resolves I/J/K later.  The forall symtab binds each
         loop-var name (not the __forall_lb/ub_* relays) to the generator
         compound (gen_nid) at its output port. *)
      let env_loop =
        let cs, _ = loop_gr.symtab in
        SM.fold (fun name v e ->
          let is_relay =
            String.length name >= 8 && String.sub name 0 8 = "__forall"
          in
          if v.val_def = gen_nid && not is_relay then
            { e with
              var_map =
                FullPortMap.add (sub_gid, gen_nid, v.def_port, `Out) (C.Id name)
                  e.var_map }
          else e)
          cs env_loop
      in
      (* Lower the BODY once, here at the forall scope where the loop vars I/J/K
         are bound on the generator compound.  The resulting statements reference
         I/J/K (the C loop vars), so they are valid when dropped into the
         innermost loop.  The body's output value (body_res) is what the store
         will write (next step). *)
      let body_stmts, body_res, body_tid, body_outs =
        match find_subgraph loop_gr "BODY" with
        | Some (body_nid, body_gr) ->
            let body_gid =
              try GidMap.find (sub_gid, body_nid) env.gid_table with _ -> -1
            in
            let env_body =
              { env_loop with parent_env = Some env_loop; curr_gid = body_gid;
                curr_gr = body_gr;
                parent_map =
                  IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map }
            in
            let bstmts, e_body =
              lower_graph env_body loop_gr body_nid body_gr body_gid
            in
            (* Every RETURNS-bound body output, one per `... of <expr>`, sorted by
               destination port.  A forall may return several arrays (e.g. Compute
               returns two), so collect them all -- not just the last. *)
            let outs =
              ES.fold (fun ((sn, sp), (dn, dp), t) acc ->
                if dn = 0 then (dp, get_expr e_body body_gid sn sp `Out, t) :: acc
                else acc) body_gr.eset []
              |> List.sort (fun (a, _, _) (b, _, _) -> compare a b)
            in
            let bres, btid =
              match outs with (_, e, t) :: _ -> (e, t) | [] -> (C.LitInt 0, 6)
            in
            (bstmts, bres, btid, outs)
        | None -> ([], C.LitInt 0, 6, [])
      in
      (* The result element type comes from the body's output port; the store
         writes SISAL_CAST(elem, body_res) into the result's data buffer. *)
      let tm = get_typemap_tm loop_gr in
      let out_ty =
        try c_type_of_if1_ty tm (TM.find body_tid tm) with _ -> C.Basic "int32_t"
      in
      let res_v = C.Id (get_c_name env.proc_map env.gid_name_map gid nid 0 `Out gr) in
      let cast_body_res =
        C.Call ("SISAL_CAST", [ C.Id (string_of_c_type out_ty); body_res ])
      in
      (* The (first) induction-var name -- argmax/argmin return this Sisal index. *)
      let loop_var_name =
        let cs, _ = loop_gr.symtab in
        SM.fold (fun name v acc ->
          match acc with
          | Some _ -> acc
          | None ->
              let is_relay =
                String.length name >= 8 && String.sub name 0 8 = "__forall"
              in
              if v.val_def = gen_nid && not is_relay then Some name else None)
          cs None
      in
      let ret_opt =
        match find_subgraph loop_gr "RETURNS" with
        | Some (_, rg) -> Some rg
        | None -> None
      in
      (* MULTI-REDUCTION forall (e.g. `returns value of sum i  value of product i`):
         forall_fold_op only fires for ONE reduction output; for several it returns
         None and the gather path wrongly allocs an array per reduction.  Lower each
         reduction output as its own scalar accumulator instead.  (All-reduction case
         here; mixed gather+reduce is the next step.) *)
      let reduce_ports = forall_reduce_ports loop_gr in
      let n_out_ports =
        match ret_opt with
        | Some rg -> ES.fold (fun ((sn, _), (dn, dp), _) acc ->
            if dn = 0 && sn <> 0 then IntSet.add dp acc else acc) rg.eset IntSet.empty
                     |> IntSet.cardinal
        | None -> 0 in
      if List.length reduce_ports > 1 && List.length reduce_ports = n_out_ports then (
        let scope = scope_of env.gid_name_map sub_gid in
        let inf_pos oty = match oty with
          | C.Basic "double" -> C.Id "1e308"
          | C.Basic "float" -> C.Id "3.4028235e+38f"
          | _ -> C.Id "0x7fffffff" in
        let body_val bport =
          match List.find_opt (fun (p, _, _) -> p = bport) body_outs with
          | Some (_, e, t) -> (e, t)
          | None -> (match body_outs with (_, e, t) :: _ -> (e, t) | [] -> (C.LitInt 0, 6)) in
        let parts = List.map (fun (dp, op, _bport) ->
          let e, t = body_val dp in
          let oty = try c_type_of_if1_ty tm (TM.find t tm) with _ -> C.Basic "int32_t" in
          let rv = C.Id (get_c_name env.proc_map env.gid_name_map gid nid dp `Out gr) in
          let cbody = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type oty); e ]) in
          match op with
          | "argmax" | "argmin" ->
              let accv = Printf.sprintf "__argm_val_%s_%d" scope dp in
              let sentinel = if op = "argmax" then C.UnaryOp (C.Negate, inf_pos oty) else inf_pos oty in
              let cmp = if op = "argmax" then C.Gt else C.Lt in
              let idx = match loop_var_name with Some n -> C.Id n | None -> C.LitInt 0 in
              ( [ C.Decl (oty, accv, Some sentinel) ],
                [ C.Expr (C.BinOp (C.Assign, rv, C.LitInt 0)) ],
                [ C.If (C.BinOp (cmp, cbody, C.Id accv),
                    [ C.Expr (C.BinOp (C.Assign, C.Id accv, cbody));
                      C.Expr (C.BinOp (C.Assign, rv, idx)) ], []) ] )
          | _ ->
              let init_val = match op with
                | "product" -> C.LitInt 1 | "least" -> inf_pos oty
                | "greatest" -> C.UnaryOp (C.Negate, inf_pos oty) | _ -> C.LitInt 0 in
              let update = match op with
                | "product" -> C.Expr (C.BinOp (C.Assign, rv, C.BinOp (C.Mul, rv, cbody)))
                | "least" -> C.If (C.BinOp (C.Lt, cbody, rv), [ C.Expr (C.BinOp (C.Assign, rv, cbody)) ], [])
                | "greatest" -> C.If (C.BinOp (C.Gt, cbody, rv), [ C.Expr (C.BinOp (C.Assign, rv, cbody)) ], [])
                | _ -> let o2 = if oty = C.Basic "bool" then C.LogOr else C.Add in
                       C.Expr (C.BinOp (C.Assign, rv, C.BinOp (o2, rv, cbody))) in
              ( [], [ C.Expr (C.BinOp (C.Assign, rv, init_val)) ], [ update ] ))
          reduce_ports in
        let decls = List.concat (List.map (fun (d, _, _) -> d) parts) in
        let inits = List.concat (List.map (fun (_, i, _) -> i) parts) in
        let updates = List.concat (List.map (fun (_, _, u) -> u) parts) in
        let make_inner _off = body_stmts @ updates in
        let prelude, nest_stmts, _extents, env_loop =
          zip_loops env_loop loop_gr sub_gid gen_nid gen_gr ret_opt None make_inner in
        (decl_stmts @ loop_in_stmts @ prelude @ decls @ inits @ nest_stmts @ fanout_stmts,
         { env_loop with curr_gid = gid; curr_gr = gr; parent_env = env.parent_env }))
      else
      (match forall_fold_op loop_gr with
      | Some op ->
          (* Reduction: fold the body value into a scalar accumulator at the
             innermost loop -- no array alloc/store.  sum/product/least/greatest
             accumulate into the result var; argmax/argmin carry a best-value plus
             the result (the Sisal index of the extremum). *)
          let scope = scope_of env.gid_name_map sub_gid in
          let inf_pos =
            match out_ty with
            | C.Basic "double" -> C.Id "1e308"
            | C.Basic "float" -> C.Id "3.4028235e+38f"
            | _ -> C.Id "0x7fffffff"
          in
          let pre, make_inner =
            match op with
            | "argmax" | "argmin" ->
                let acc_val = Printf.sprintf "__argm_val_%s" scope in
                let sentinel =
                  if op = "argmax" then C.UnaryOp (C.Negate, inf_pos) else inf_pos
                in
                let cmp = if op = "argmax" then C.Gt else C.Lt in
                let idx =
                  match loop_var_name with Some n -> C.Id n | None -> C.LitInt 0
                in
                ( [ C.Decl (out_ty, acc_val, Some sentinel);
                    C.Expr (C.BinOp (C.Assign, res_v, C.LitInt 0)) ],
                  fun _off ->
                    body_stmts
                    @ [ C.If
                          ( C.BinOp (cmp, cast_body_res, C.Id acc_val),
                            [ C.Expr (C.BinOp (C.Assign, C.Id acc_val, cast_body_res));
                              C.Expr (C.BinOp (C.Assign, res_v, idx)) ],
                            [] ) ] )
            | _ ->
                let init_val =
                  match op with
                  | "product" -> C.LitInt 1
                  | "least" -> inf_pos
                  | "greatest" -> C.UnaryOp (C.Negate, inf_pos)
                  | _ -> C.LitInt 0
                in
                let update =
                  match op with
                  | "product" ->
                      C.Expr (C.BinOp (C.Assign, res_v, C.BinOp (C.Mul, res_v, cast_body_res)))
                  | "least" ->
                      C.If (C.BinOp (C.Lt, cast_body_res, res_v),
                        [ C.Expr (C.BinOp (C.Assign, res_v, cast_body_res)) ], [])
                  | "greatest" ->
                      C.If (C.BinOp (C.Gt, cast_body_res, res_v),
                        [ C.Expr (C.BinOp (C.Assign, res_v, cast_body_res)) ], [])
                  | _ ->
                      let op2 = if out_ty = C.Basic "bool" then C.LogOr else C.Add in
                      C.Expr (C.BinOp (C.Assign, res_v, C.BinOp (op2, res_v, cast_body_res)))
                in
                ( [ C.Expr (C.BinOp (C.Assign, res_v, init_val)) ],
                  fun _off -> body_stmts @ [ update ] )
          in
          let prelude, nest_stmts, _extents, env_loop =
            zip_loops env_loop loop_gr sub_gid gen_nid gen_gr ret_opt None make_inner
          in
          (decl_stmts @ loop_in_stmts @ prelude @ pre @ nest_stmts @ fanout_stmts,
           { env_loop with curr_gid = gid; curr_gr = gr; parent_env = env.parent_env })
      | None ->
      (* Per-output dispatch for a possibly MIXED forall.  When there are no reduction
         outputs, keep the original all-gather behavior (one result array per body
         output).  When reductions ARE present (gather + reduce in one forall, e.g. the
         broadcast conform loop `array_dv of shape  value of least compat`), lower each
         output by its kind: gather outputs -> alloc/store (per_out), reduction outputs
         -> scalar accumulators (the red_ bindings), interleaved in one loop body. *)
      let reduce_specs = forall_reduce_ports loop_gr in
      let gather_specs = forall_gather_ports loop_gr in
      (* The body value for an output is body_outs[output_port] -- the forall output
         port maps 1:1 to the body output port (same as the all-gather path).  The
         __forall_body_K index the classifiers also return is unreliable here, so use
         the output port directly. *)
      let body_val bp =
        match List.find_opt (fun (p, _, _) -> p = bp) body_outs with
        | Some (_, e, t) -> (e, t)
        | None -> (match body_outs with (_, e, t) :: _ -> (e, t) | [] -> (C.LitInt 0, 6)) in
      let gather_src =
        if reduce_specs = [] then body_outs
        else List.map (fun (out_port, _bp) -> let (e, t) = body_val out_port in (out_port, e, t)) gather_specs in
      let per_out =
        List.map (fun (dp, bres, btid) ->
          let oty = try c_type_of_if1_ty tm (TM.find btid tm) with _ -> C.Basic "int32_t" in
          let rv = C.Id (get_c_name env.proc_map env.gid_name_map gid nid dp `Out gr) in
          let cast = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type oty); bres ]) in
          (rv, oty, btid, cast))
          gather_src
      in
      let red_scope = scope_of env.gid_name_map sub_gid in
      let red_inf oty = match oty with
        | C.Basic "double" -> C.Id "1e308" | C.Basic "float" -> C.Id "3.4028235e+38f"
        | _ -> C.Id "0x7fffffff" in
      let red_decls, red_inits, red_updates =
        List.fold_left (fun (ds, is, us) (dp, op, _bp) ->
          let e, t = body_val dp in
          let oty = try c_type_of_if1_ty tm (TM.find t tm) with _ -> C.Basic "int32_t" in
          let rv = C.Id (get_c_name env.proc_map env.gid_name_map gid nid dp `Out gr) in
          let cb = C.Call ("SISAL_CAST", [ C.Id (string_of_c_type oty); e ]) in
          match op with
          | "argmax" | "argmin" ->
              let accv = Printf.sprintf "__argm_val_%s_%d" red_scope dp in
              let sentinel = if op = "argmax" then C.UnaryOp (C.Negate, red_inf oty) else red_inf oty in
              let cmp = if op = "argmax" then C.Gt else C.Lt in
              let idx = match loop_var_name with Some n -> C.Id n | None -> C.LitInt 0 in
              ( ds @ [ C.Decl (oty, accv, Some sentinel) ],
                is @ [ C.Expr (C.BinOp (C.Assign, rv, C.LitInt 0)) ],
                us @ [ C.If (C.BinOp (cmp, cb, C.Id accv),
                         [ C.Expr (C.BinOp (C.Assign, C.Id accv, cb));
                           C.Expr (C.BinOp (C.Assign, rv, idx)) ], []) ] )
          | _ ->
              let init_val = match op with
                | "product" -> C.LitInt 1 | "least" -> red_inf oty
                | "greatest" -> C.UnaryOp (C.Negate, red_inf oty) | _ -> C.LitInt 0 in
              let update = match op with
                | "product" -> C.Expr (C.BinOp (C.Assign, rv, C.BinOp (C.Mul, rv, cb)))
                | "least" -> C.If (C.BinOp (C.Lt, cb, rv), [ C.Expr (C.BinOp (C.Assign, rv, cb)) ], [])
                | "greatest" -> C.If (C.BinOp (C.Gt, cb, rv), [ C.Expr (C.BinOp (C.Assign, rv, cb)) ], [])
                | _ -> let o2 = if oty = C.Basic "bool" then C.LogOr else C.Add in
                       C.Expr (C.BinOp (C.Assign, rv, C.BinOp (o2, rv, cb))) in
              ( ds, is @ [ C.Expr (C.BinOp (C.Assign, rv, init_val)) ], us @ [ update ] ))
          ([], [], []) reduce_specs
      in
      let make_inner off =
        body_stmts
        @ List.map (fun (rv, oty, _, cast) ->
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     C.Index
                       (C.Cast (C.Pointer (oty, []), C.Member (rv, "data")), off),
                     cast )))
            per_out
        @ red_updates
      in
      let prelude, nest_stmts, extents, env_loop =
        zip_loops env_loop loop_gr sub_gid gen_nid gen_gr ret_opt None make_inner
      in
      (* Allocate the result descriptor before the nest.  The dims/count need each
         axis's bounds in the FORALL scope (the inner ub is loop-local), so walk
         the generator nest and resolve each level's primary RANGEGEN bound up to
         the forall through the compound ladder.  The store OFFSET stays in-scope
         (Horner, built inside the loops). *)
      let feed_of g dnode dport =
        ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
          if dn = dnode && dp = dport then Some (sn, sp) else acc) g.eset None
      in
      (* Follow a generator-bound source up the compound ladder (innermost-first,
         last entry's graph = loop_gr) to the forall scope; non-boundary sources
         (literals) fall back to the gen-scope value the zip already resolved. *)
      let rec resolve_up (sn, sp) ladder fallback =
        if sn <> 0 then fallback
        else
          match ladder with
          | [] -> fallback
          | (comp, pg) :: rest -> (
              match feed_of pg comp sp with
              | Some (psn, psp) ->
                  if rest = [] then get_expr env_loop sub_gid psn psp `Out
                  else resolve_up (psn, psp) rest fallback
              | None -> fallback)
      in
      (* One (lb, ub) per result dimension, forall-scope, outer -> inner. *)
      let fa_extents =
        let rec walk g comp pgraph parent_ladder fbs acc =
          let ladder = (comp, pgraph) :: parent_ladder in
          let rg =
            NM.fold (fun n nd a ->
              match (a, nd) with
              | Some _, _ -> a
              | None, Simple (_, RANGEGEN, _, _, _) -> Some n
              | _ -> None) g.nmap None
          in
          let fb_lb, fb_ub =
            match fbs with x :: _ -> x | [] -> (C.LitInt 1, C.LitInt 0)
          in
          let entry =
            match rg with
            | Some r ->
                let lbf =
                  match feed_of g r 0 with
                  | Some s -> resolve_up s ladder fb_lb | None -> fb_lb
                in
                let ubf =
                  match feed_of g r 1 with
                  | Some s -> resolve_up s ladder fb_ub | None -> fb_ub
                in
                [ (lbf, ubf) ]
            | None -> []
          in
          let fbs' = match fbs with _ :: t -> t | [] -> [] in
          match find_subgraph g "GENERATOR" with
          | Some (inner_nid, inner_gr) ->
              walk inner_gr inner_nid g ladder fbs' (acc @ entry)
          | None -> acc @ entry
        in
        walk gen_gr gen_nid loop_gr [] extents []
      in
      let rank = List.length fa_extents in
      let ext_of (lb, ub) =
        C.BinOp (C.Add, C.BinOp (C.Sub, ub, lb), C.LitInt 1)
      in
      let count =
        List.fold_left (fun acc e -> C.BinOp (C.Mul, acc, ext_of e))
          (C.LitInt 1) fa_extents
      in
      (* Allocate each output descriptor (shared extents/count) and fill its
         per-axis triple (start, size); stride stays 0 -- the store uses the inline
         Horner offset, not the stride field, for now. *)
      let allocs =
        List.concat
          (List.map (fun (rv, _, btid, _) ->
             let alloc =
               C.Expr (C.BinOp ( C.Assign, rv,
                 C.Call ("sisal_array_alloc_empty",
                   [ C.LitInt rank; C.LitInt btid;
                     C.Cast (C.Basic "uint64_t", count) ]) ))
             in
             let dim_sets =
               List.concat
                 (List.mapi (fun k (lb, ub) ->
                    [ C.Expr (C.BinOp (C.Assign,
                        C.Index (C.Member (rv, "dims"), C.LitInt k), ext_of (lb, ub)));
                      C.Expr (C.BinOp (C.Assign,
                        C.Index (C.Member (rv, "lower_bound"), C.LitInt k), lb)) ])
                    fa_extents)
             in
             alloc :: dim_sets)
            per_out)
      in
      (* BOX-then-FLATTEN: a DV_GATHER increments rank.  When the gathered body
         value is itself an array_dv (e.g. `returns array_dv of <inner forall row>`),
         the loop above BOXED rows -- it stored row DESCRIPTORS into rv (rank = outer
         axes).  Re-pack them into a flat rank-(outer + elem.rank) array_dv, reading
         the element shape ONCE off the first boxed row (it is rectangular, so all
         rows share rank/dims/size); the only per-row work is a memcpy of its bytes.
         Scalar gathers (oty <> sisal_array_t) skip this entirely. *)
      let sat = C.Basic "sisal_array_t" in
      let flattens =
        List.concat
          (List.map (fun (rv, oty, _, _) ->
             if oty <> sat then []
             else
               let rvn = (match rv with C.Id n -> n | _ -> "rv") in
               let e0 = C.Id ("__e0_" ^ rvn) and fl = C.Id ("__flat_" ^ rvn) in
               let esz = C.Call ("sisal_elem_size", [ C.Member (e0, "type_id") ]) in
               let ecount = C.Member (e0, "size") in
               let bytes = C.BinOp (C.Mul, ecount, esz) in
               let boxed i =
                 C.Index (C.Cast (C.Pointer (sat, []), C.Member (rv, "data")), i) in
               (* __e0 = first boxed row (its rank/dims/size describe every row) *)
               let decl_e0 = C.Decl (sat, "__e0_" ^ rvn, Some (boxed (C.LitInt 0))) in
               (* __flat = alloc_empty(rank + __e0.rank, __e0.type_id, count*__e0.size) *)
               let decl_fl =
                 C.Decl (sat, "__flat_" ^ rvn,
                   Some (C.Call ("sisal_array_alloc_empty",
                     [ C.BinOp (C.Add, C.LitInt rank, C.Member (e0, "rank"));
                       C.Member (e0, "type_id");
                       C.Cast (C.Basic "uint64_t",
                         C.BinOp (C.Mul, C.Cast (C.Basic "uint64_t", count), ecount)) ])) ) in
               (* outer axes (static) prepend the element's inner axes *)
               let outer_dims =
                 List.concat (List.mapi (fun k (lb, ub) ->
                   [ C.Expr (C.BinOp (C.Assign,
                       C.Index (C.Member (fl, "dims"), C.LitInt k), ext_of (lb, ub)));
                     C.Expr (C.BinOp (C.Assign,
                       C.Index (C.Member (fl, "lower_bound"), C.LitInt k), lb)) ])
                   fa_extents) in
               let kk = "__k_" ^ rvn in
               let inner_dims =
                 C.For (C.Decl (C.Basic "int32_t", kk, Some (C.LitInt 0)),
                   C.BinOp (C.Lt, C.Id kk, C.Member (e0, "rank")),
                   C.UnaryOp (C.PostInc, C.Id kk),
                   [ C.Expr (C.BinOp (C.Assign,
                       C.Index (C.Member (fl, "dims"), C.BinOp (C.Add, C.LitInt rank, C.Id kk)),
                       C.Index (C.Member (e0, "dims"), C.Id kk)));
                     C.Expr (C.BinOp (C.Assign,
                       C.Index (C.Member (fl, "lower_bound"), C.BinOp (C.Add, C.LitInt rank, C.Id kk)),
                       C.Index (C.Member (e0, "lower_bound"), C.Id kk))) ]) in
               let ii = "__i_" ^ rvn in
               let copy =
                 C.For (C.Decl (C.Basic "int32_t", ii, Some (C.LitInt 0)),
                   C.BinOp (C.Lt, C.Id ii, C.Cast (C.Basic "int32_t", count)),
                   C.UnaryOp (C.PostInc, C.Id ii),
                   [ C.Expr (C.Call ("memcpy",
                       [ C.BinOp (C.Add,
                           C.Cast (C.Pointer (C.Basic "char", []), C.Member (fl, "data")),
                           C.BinOp (C.Mul, C.Cast (C.Basic "uint64_t", C.Id ii), bytes));
                         C.Member (boxed (C.Id ii), "data");
                         bytes ])) ]) in
               let back = C.Expr (C.BinOp (C.Assign, rv, fl)) in
               [ decl_e0; decl_fl ] @ outer_dims @ [ inner_dims; copy; back ])
            per_out)
      in
      (decl_stmts @ loop_in_stmts @ prelude @ red_decls @ red_inits @ allocs @ nest_stmts
        @ flattens @ fanout_stmts,
       { env_loop with curr_gid = gid; curr_gr = gr; parent_env = env.parent_env }))
  | None ->
      (decl_stmts @ loop_in_stmts,
       { env_loop with curr_gid = gid; curr_gr = gr; parent_env = env.parent_env })

(* Zip the GENERATOR nest and the RETURNS nest in lockstep, one `for` per level.
   The generator side gives the loop control (induction var `ivar`, lb, ub); the
   returns side (when present at this level) contributes a 0-based returns
   counter `__r<ivar>` carried alongside -- redundant with `ivar - lb` for Sisal
   1.2, but the decoupling hook for 2.0.  When one nest runs out we keep
   descending the other:
     - both present  -> recurse both;
     - generator deeper (returns ran out, e.g. a reduction) -> loop with NO
       returns counter;
     - returns deeper (generator ran out, Sisal 2.0 size-descriptor) -> stub.
   ret_gr_opt is the returns subgraph for THIS level (None once it's run out). *)
and zip_loops env parent_gr parent_gid gen_nid gen_gr ret_gr_opt offset_acc make_inner =
  let gen_gid = try GidMap.find (parent_gid, gen_nid) env.gid_table with _ -> -1 in
  let env_gen =
    { env with parent_env = Some env; compound_nid_in_parent = gen_nid;
      curr_gid = gen_gid; curr_gr = gen_gr;
      parent_map = IntMap.add gen_gid (parent_gid, gen_nid) env.parent_map }
  in
  let gen_in_stmts, env_gen =
    init_boundary_ports env_gen parent_gr gen_nid gen_gr gen_gid
  in
  (* Lower the GENERATOR as a full graph: topo-walk its edges and lower every
     non-RANGEGEN Simple node (the loop-bound computations, e.g. `n - 1` for
     `for i in 1, n-1`) in data-dependence order, so each bound is DECLARED as a
     C variable before anything references it.  RANGEGEN itself becomes the `for`
     statement (below), so it is skipped here; nested GENERATOR/BODY compounds are
     handled by `recurse`, so Compounds are skipped too.  These declarations form
     the generator's contribution to the forall scaffold (the `prelude`), hoisted
     ahead of the result alloc by the caller; the `for` statement's lb/ub then
     thread from these declared bound values via `src_of`. *)
  let bound_stmts, env_gen =
    (* Walk the generator's edges in data-dependence order.  Each edge carries a
       value from its TAIL (producer) to its HEAD (consumer).  When the tail is a
       dataflow Simple node we haven't emitted yet, lower it -- that DECLARES the
       bound math (e.g. `n-1`) before the `for`/alloc thread it.  Tails we skip:
       the boundary (graph inputs, already bound), the RANGEGEN axis (it becomes
       the `for`), nested GENERATOR compounds (handled by `recurse`), and literals
       (inlined by get_expr where used). *)
    let lowered = ref IntSet.empty in
    List.fold_left (fun (acc, e) ((sn, _), (_dn, _dp), _) ->
      if sn = 0 || IntSet.mem sn !lowered then (acc, e)
      else match NM.find_opt sn gen_gr.nmap with
        | Some (Simple (_, RANGEGEN, _, _, _)) -> (acc, e)
        | Some (Simple _ as node) ->
            lowered := IntSet.add sn !lowered;
            let s, e' = lower_node e gen_gr sn node in (acc @ s, e')
        | _ -> (acc, e))
      ([], env_gen) (topo_sort_edges gen_gr)
  in
  (* All RANGEGENs at THIS generator level.  One axis per level = a cross
     (nesting); several axes at the SAME level = a `dot` (zip): one loop whose
     counter drives every axis in lockstep. *)
  let rangegens =
    NM.fold (fun n node acc ->
      match node with Simple (_, RANGEGEN, _, _, _) -> n :: acc | _ -> acc)
      gen_gr.nmap []
  in
  let name_of rg =
    let cs, _ = gen_gr.symtab in
    match
      SM.fold (fun name v acc ->
        match acc with
        | Some _ -> acc
        | None -> if v.val_def = rg && v.def_port = 0 then Some name else None)
        cs None
    with
    | Some nm -> nm
    | None -> Printf.sprintf "__iv_%d" rg
  in
  (* value feeding RANGEGEN input `port` (0 = lb, 1 = ub); get_expr resolves the
     literal "1" and the wired boundary inputs. *)
  let src_of rg port dflt =
    match
      ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = rg && dp = port then Some (sn, sp) else acc)
        gen_gr.eset None
    with
    | Some (sn, sp) -> get_expr env_gen gen_gid sn sp `Out
    | None -> dflt
  in
  (* This level has a returns dimension iff a returns subgraph was handed down. *)
  let has_returns = ret_gr_opt <> None in
  let inner_gen = find_subgraph gen_gr "GENERATOR" in
  let inner_ret =
    match ret_gr_opt with Some rg -> find_subgraph rg "RETURNS" | None -> None
  in
  (* Recurse one level deeper (or, at the innermost generator, place the body +
     store via make_inner), carrying the row-major offset accumulated so far. *)
  let recurse off =
    match (inner_gen, inner_ret) with
    | Some (ign, igr), Some (_, irgr) ->
        zip_loops env_gen gen_gr gen_gid ign igr (Some irgr) off make_inner
    | Some (ign, igr), None ->
        zip_loops env_gen gen_gr gen_gid ign igr None off make_inner
    | None, Some _ ->
        ( [],
          make_inner (Option.value off ~default:(C.LitInt 0))
          @ [ C.Comment "TODO: returns deeper than generator (Sisal 2.0 size-descriptor)" ],
          [], env_gen )
    | None, None -> ([], make_inner (Option.value off ~default:(C.LitInt 0)), [], env_gen)
  in
  match rangegens with
  | [] ->
      (* No range axis at this level (e.g. element scatter `for x in A`) -- TODO;
         pass through unchanged, offset unchanged. *)
      let inner_prelude, inner_stmts, inner_exts, _ = recurse offset_acc in
      (gen_in_stmts @ bound_stmts @ inner_prelude, inner_stmts, inner_exts, env_gen)
  | primary :: siblings ->
      (* The primary RANGEGEN drives the loop; dot siblings advance in lockstep:
         sib = sib_lb + (primary - primary_lb). *)
      let ivar = name_of primary in
      let lb_expr = src_of primary 0 (C.LitInt 1) in
      let ub_expr = src_of primary 1 (C.LitInt 0) in
      (* Counter name is per-generator so multiple foralls in one scope (e.g. A,
         B, C in a matmul `let`) don't redefine __rI/__rJ/... *)
      let ri = Printf.sprintf "__r%d_%s" gen_gid ivar in
      let ext_expr =
        C.BinOp (C.Add, C.BinOp (C.Sub, ub_expr, lb_expr), C.LitInt 1)
      in
      (* Fold this gather dimension into the row-major store offset (Horner):
         the first dimension is just its counter, each deeper dimension is
         acc*extent + counter. *)
      let off' =
        if has_returns then
          Some
            (match offset_acc with
             | None -> C.Id ri
             | Some a -> C.BinOp (C.Add, C.BinOp (C.Mul, a, ext_expr), C.Id ri))
        else offset_acc
      in
      let inner_prelude, inner_stmts, inner_exts, _ = recurse off' in
      let sibling_decls =
        List.map (fun rg ->
          let jvar = name_of rg in
          let jlb = src_of rg 0 (C.LitInt 1) in
          C.Decl
            ( C.Basic "int32_t", jvar,
              Some (C.BinOp (C.Add, jlb, C.BinOp (C.Sub, C.Id ivar, lb_expr))) ))
          siblings
      in
      let body =
        sibling_decls @ inner_stmts
        @ (if has_returns then [ C.Expr (C.UnaryOp (C.PostInc, C.Id ri)) ] else [])
      in
      let loop =
        C.For
          ( C.Decl (C.Basic "int32_t", ivar, Some lb_expr),
            C.BinOp (C.Le, C.Id ivar, ub_expr),
            C.UnaryOp (C.PostInc, C.Id ivar),
            body )
      in
      (* The generator's scaffold (boundary imports + bound math + any hoisted
         inner-generator scaffold) becomes the PRELUDE -- emitted by the caller
         BEFORE the result alloc, since the alloc's extents thread from these
         bound values.  The `ri` reset stays loop-local (inside the parent's loop
         body via `inner_stmts`) so a nested gather counter resets each outer pass. *)
      let prelude = gen_in_stmts @ bound_stmts @ inner_prelude in
      let loop_pre =
        if has_returns then [ C.Decl (C.Basic "int32_t", ri, Some (C.LitInt 0)) ]
        else []
      in
      (* A gather level contributes one result dimension: extent = ub - lb + 1.
         A `dot` is one dimension (the siblings advance in lockstep), so only the
         primary axis's bounds count.  Reductions (has_returns over a non-gather)
         carry no array dimension -- handled on the reduction path, not here. *)
      let this_ext = if has_returns then [ (lb_expr, ub_expr) ] else [] in
      (prelude, loop_pre @ [ loop ], this_ext @ inner_exts, env_gen)

(* ============== OLD lower_forall (single flat loop) — reference ==============
and lower_forall_OLD env gr gid nid loop_gr sub_gid pr =
  let env_init = { env with parent_env = Some env; compound_nid_in_parent = nid; curr_gid = sub_gid; curr_gr = loop_gr } in
  let env_init = scan_fanout loop_gr sub_gid env_init in
  let node = match NM.find_opt nid gr.nmap with Some n -> n | _ -> failwith "no node" in
  let decl_stmts, env_init = declare_outputs env_init gr gid nid node in
  let loop_in_stmts, env_loop = init_boundary_ports env_init gr nid loop_gr sub_gid in
  let gen_nid, gen_gr = match find_subgraph loop_gr "GENERATOR" with | Some x -> x | _ -> failwith "no GEN" in
  let gen_gid = try GidMap.find (sub_gid, gen_nid) env.gid_table with _ -> -1 in
  let env_gen = { env_loop with parent_env = Some env_loop; curr_gid = gen_gid; curr_gr = gen_gr; parent_map = IntMap.add gen_gid (sub_gid, gen_nid) env_loop.parent_map } in
  let gen_stmts, e_gen = lower_graph env_gen loop_gr gen_nid gen_gr gen_gid in
  (* Extent is the output of the generator's RANGEGEN/DV_SCATTER/ASCATTER node.
     Find that node directly rather than trusting a boundary-output port order
     (generator outputs are now emitted in symtab-map order, so out 0 is not
     guaranteed to be the extent). RANGEGEN:0 -> (hi-lo)+1; DV_SCATTER:0 -> A.size. *)
  let count =
    let ext_node =
      NM.fold (fun nid n acc ->
        match acc with
        | Some _ -> acc
        | None -> (match n with
            | Simple (_, (RANGEGEN | DV_SCATTER | ASCATTER), _, _, _) -> Some nid
            | _ -> None))
        gen_gr.nmap None
    in
    match ext_node with
    | Some nid -> get_expr e_gen gen_gid nid 0 `Out
    | None ->
        (match ES.fold (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc) gen_gr.eset None with
         | Some (sn, sp) -> get_expr e_gen gen_gid sn sp `Out
         | None -> C.LitInt 0) in
  let env_loop = { env_loop with var_map = e_gen.var_map; type_table = e_gen.type_table; seen_decls = e_gen.seen_decls } in

  let body_nid, body_gr = match find_subgraph loop_gr "BODY" with | Some x -> x | _ -> failwith "no BODY" in
  let body_gid = try GidMap.find (sub_gid, body_nid) env.gid_table with _ -> -1 in
  let _idx_port = ES.fold (fun ((sn, _), (dn, dp), _) acc -> if sn = gen_nid && dn = body_nid then Some dp else acc) loop_gr.eset None |> Option.value ~default:0 in
  let loop_idx_var = Printf.sprintf "__idx_%s" (scope_of env.gid_name_map sub_gid) in
  (* Lower bound from GENERATOR node 1 (the literal that feeds RANGEGEN port 0). *)
  let lb_expr = match FullPortMap.find_opt (gen_gid, 1, 0, `Out) e_gen.var_map with
    | Some ex -> ex | None -> C.LitInt 0 in
  (* Wire any loop_gr boundary ports that weren't provided by the parent graph.
     Standard forall: loop variable = lb + loop_counter (index-based).
     DV element forall ("for i in A dot j in B"): loop variable = A.data[loop_counter] (element). *)
  (* Install per-iteration loop-variable values at the GENERATOR compound's
     output ports (sub_gid, gen_nid, op).  The generator's outputs (induction
     vars, range bounds, scatter elements, at indices) are now defined by the
     generator compound, so the body reads them from there.  Driven by the
     generator's RANGEGEN / DV_SCATTER nodes, so it scales to dot (N axes). *)
  let env_loop =
    let tm = get_typemap_tm loop_gr in
    let gen_out_port gnode gport =
      ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if sn = gnode && sp = gport && dn = 0 then Some dp else acc) gen_gr.eset None in
    let val_into gnode gport =
      match ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = gnode && dp = gport then Some (sn, sp) else acc) gen_gr.eset None with
      | Some (sn, sp) -> get_expr e_gen gen_gid sn sp `Out
      | None -> C.LitInt 0 in
    let out_ty_id gnode gport =
      ES.fold (fun ((sn, sp), (dn, _), t) acc ->
        if sn = gnode && sp = gport && dn = 0 then t else acc) gen_gr.eset 0 in
    let bind gnode gport ex e =
      match gen_out_port gnode gport with
      | Some op -> { e with var_map = FullPortMap.add (sub_gid, gen_nid, op, `Out) ex e.var_map }
      | None -> e in
    NM.fold (fun gnode gnode_v e ->
      match gnode_v with
      | Simple (_, RANGEGEN, _, _, _) ->
          (* out 0 = induction var = lb + idx ; out 1 = lb ; out 2 = ub *)
          let lb_k = val_into gnode 0 in
          let ub_k = val_into gnode 1 in
          let e = bind gnode 0 (C.BinOp (C.Add, lb_k, C.Id loop_idx_var)) e in
          let e = bind gnode 1 lb_k e in
          bind gnode 2 ub_k e
      | Simple (_, (DV_SCATTER | ASCATTER), _, outs, _) ->
          (* out 0 = element = A.data[idx] cast to elem ; out p>=1 = at index = A.lb + idx *)
          let arr_expr = val_into gnode 0 in
          snd (Array.fold_left (fun (p, e) _ ->
            let ex =
              if p = 0 then
                let elem_ty =
                  try c_type_of_if1_ty tm (TM.find (out_ty_id gnode 0) tm)
                  with _ -> C.Basic "int32_t" in
                C.Index (C.Cast (C.Pointer (elem_ty, []), C.Member (arr_expr, "data")), C.Id loop_idx_var)
              else
                C.BinOp (C.Add, C.Cast (C.Basic "int32_t", C.Index (C.Member (arr_expr, "lower_bound"), C.LitInt 0)), C.Id loop_idx_var)
            in
            (p + 1, bind gnode p ex e)) (0, e) outs)
      | _ -> e
    ) gen_gr.nmap env_loop in

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
  (* The body's loop-variable inputs are wired by init_boundary_ports from the
     generator compound outputs (sub_gid, gen_nid, op) bound above to lb+idx /
     element / at-index.  Only register the loop counter as declared. *)
  let env_body = { env_body with
    seen_decls = StringSet.add loop_idx_var env_body.seen_decls } in
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
  | Some ("argmax" | "argmin" as op_name) ->
      (* Argmax/argmin fold: carry both running-best-value and best-index.
         Body expression yields the value to compare; result is the 1-based Sisal index. *)
      let scope = scope_of env.gid_name_map sub_gid in
      let acc_val_var = Printf.sprintf "__argm_val_%s" scope in
      let acc_idx_var = Printf.sprintf "__argm_idx_%s" scope in
      let neg_inf = match out_ty with
        | C.Basic "double" -> C.UnaryOp (C.Negate, C.Id "1e308")
        | C.Basic "float"  -> C.UnaryOp (C.Negate, C.Id "3.4028235e+38f")
        | _                -> C.UnaryOp (C.Negate, C.Id "0x7fffffff") in
      let pos_inf = match out_ty with
        | C.Basic "double" -> C.Id "1e308"
        | C.Basic "float"  -> C.Id "3.4028235e+38f"
        | _                -> C.Id "0x7fffffff" in
      let init_sentinel = if op_name = "argmax" then neg_inf else pos_inf in
      let cmp_op = if op_name = "argmax" then C.Gt else C.Lt in
      let acc_val_decl = C.Decl (out_ty, acc_val_var, Some init_sentinel) in
      let acc_idx_decl = C.Decl (C.Basic "int32_t", acc_idx_var, Some (C.LitInt 0)) in
      (* 1-based Sisal index = loop_idx_var (0-based counter) + lb_expr *)
      let sisal_idx = C.BinOp (C.Add, C.Id loop_idx_var, lb_expr) in
      let update_val = C.BinOp (C.Assign, C.Id acc_val_var, cast_body_res) in
      let update_idx = C.BinOp (C.Assign, C.Id acc_idx_var, sisal_idx) in
      let update_if = C.If (C.BinOp (cmp_op, cast_body_res, C.Id acc_val_var),
                            [ C.Expr update_val; C.Expr update_idx ], []) in
      let loop = C.For (C.Decl (C.Basic "int32_t", loop_idx_var, Some (C.LitInt 0)),
                        C.BinOp (C.Lt, C.Id loop_idx_var, count),
                        C.BinOp (C.Assign, C.Id loop_idx_var, C.BinOp (C.Add, C.Id loop_idx_var, C.LitInt 1)),
                        lfi_stmts @ body_stmts @ [ update_if ]) in
      let assign_result_stmts, final_env =
        let stmts, e' = assign_with_cast { e_body with curr_gid = gid; curr_gr = gr } gid nid 0 `Out (C.Id acc_idx_var) in
        (stmts, e') in
      (decl_stmts @ [ C.Compound (loop_in_stmts @ gen_stmts @ stmts_alloc @ [ acc_val_decl; acc_idx_decl; loop ] @ assign_result_stmts) ], final_env)
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
============== END OLD lower_forall ============== *)

and lower_for_initial env gr gid nid loop_gr sub_gid pr =
  let env_init_base = { env with parent_env = Some env; compound_nid_in_parent = nid; curr_gid = sub_gid; curr_gr = loop_gr } in
  let env_init_base = scan_fanout loop_gr sub_gid env_init_base in
  let node = match NM.find_opt nid gr.nmap with Some n -> n | _ -> failwith "no node" in
  let decl_stmts, env_init_base = declare_outputs env_init_base gr gid nid node in
  let loop_in_stmts, env_loop = init_boundary_ports env_init_base gr nid loop_gr sub_gid in
  (* Declare the LoopB scope's own local symtab entries at the top of the for-initial
     scope (the subgraphs INIT/BODY/TEST/RETURNS already get this via lower_graph's
     call to pre_declare_graph_locals; the loop_gr level did not until now). *)
  let loop_local_decls, env_loop = pre_declare_graph_locals env_loop loop_gr sub_gid in
  (* The loop-carried state lives in the MERGE (phi) nodes of loop_gr, which are NOT
     symtab entries (the loop_gr local symtab only holds the loop input/result). Emit one
     declarator per MERGE at the top of the for-initial scope, and bind it into var_map /
     type_table / seen_decls at the MERGE's output port so TEST/BODY/RETURNS consumers
     resolve to this carry variable. Each MERGE corresponds to one INIT output. *)
  let loop_tm = get_typemap_tm loop_gr in
  let merge_decls, env_loop =
    NM.fold (fun mnid mnode (acc, e) ->
      match mnode with
      | Simple (_, MERGE, _, _, mpr) ->
          let raw = List.find_map (function Name n -> Some n | _ -> None) mpr
                    |> Option.value ~default:(Printf.sprintf "merge_%d" mnid) in
          let vname = Printf.sprintf "v_%s_n__%d_%s" (scope_of e.gid_name_map sub_gid) mnid (sanitize raw) in
          if StringSet.mem vname e.seen_decls then (acc, e)
          else
            let ty =
              match ES.fold (fun ((sn, sp), _, t) a -> if sn = mnid && sp = 0 && t <> 0 then Some t else a) loop_gr.eset None with
              | Some t -> (try c_type_of_if1_ty loop_tm (TM.find t loop_tm) with _ -> C.Basic "int32_t")
              | None -> C.Basic "int32_t" in
            let init_val = if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
            let e' = { e with
              seen_decls = StringSet.add vname e.seen_decls;
              var_map = FullPortMap.add (sub_gid, mnid, 0, `Out) (C.Id vname) e.var_map;
              type_table = FullPortMap.add (sub_gid, mnid, 0, `Out) ty e.type_table } in
            (acc @ [ C.Decl (ty, vname, init_val) ], e')
      | _ -> (acc, e)
    ) loop_gr.nmap ([], env_loop) in
  (* Helper: find C expression for subgraph boundary output port op after lowering *)
  let get_sub_out_expr sub_gid_x nid_x sub_gr_x e_sub op =
    match FullPortMap.find_opt (sub_gid_x, 0, op, `In) e_sub.var_map with
    | Some expr -> Some expr
    | None ->
        (match ES.fold (fun ((sn, sp), (dn, dp), _) a ->
           if dn = 0 && dp = op then Some (sn, sp) else a) sub_gr_x.eset None with
         | Some (sn, sp) -> FullPortMap.find_opt (sub_gid_x, sn, sp, `Out) e_sub.var_map
         | None ->
             (* Try looking up via compound output edge in loop_gr *)
             (match ES.fold (fun ((sn, sp), (dn, dp), _) a ->
                if sn = nid_x && sp = op then Some (dn, dp) else a) loop_gr.eset None with
              | Some _ -> None
              | None -> None))
  in
  (* Bug 5: helper to copy subgraph outputs to carry-slot var_map entries.
     For each edge (subgraph_nid:op) → (0:cp) in loop_gr, find the C expression
     for subgraph output op and assign it to var_map[(sub_gid, 0, cp, Out)]. *)
  let update_carry_slots sub_nid sub_gid_x sub_gr_x e_sub e_outer =
    ES.fold (fun ((sn, sp), (dn, dp), _) (acc_stmts, e) ->
      if sn = sub_nid && dn = 0 then
        match get_sub_out_expr sub_gid_x sub_nid sub_gr_x e_sub sp with
        | Some src_expr ->
            let stmts, e' = assign_with_cast e sub_gid 0 dp `Out src_expr in
            (acc_stmts @ stmts, e')
        | None -> (acc_stmts, e)
      else (acc_stmts, e))
    loop_gr.eset ([], e_outer)
  in
  let init_nid, init_gr = match find_subgraph loop_gr "INIT" with | Some x -> x | _ -> failwith "no INIT" in
  let init_gid = try GidMap.find (sub_gid, init_nid) env.gid_table with _ -> -1 in
  let env_init = { env_loop with parent_env = Some env_loop; curr_gid = init_gid; curr_gr = init_gr; parent_map = IntMap.add init_gid (sub_gid, init_nid) env_loop.parent_map } in
  let init_stmts, e_init = lower_graph env_init loop_gr init_nid init_gr init_gid in
  let env_loop = { env_loop with var_map = e_init.var_map; type_table = e_init.type_table; seen_decls = e_init.seen_decls } in
  (* Bug 5: after INIT, initialise carry-slot C variables from INIT outputs *)
  let carry_init_stmts, env_loop =
    update_carry_slots init_nid init_gid init_gr e_init env_loop
  in
  (* Front-edge seeding: copy each MERGE phi's initial value (input port 1, sourced from an
     INIT boundary output) into the MERGE variable BEFORE the loop runs. This is the entry
     counterpart to the backedge copies; together they replace the MERGE_first select.
     INIT statements are emitted flat in the LoopB scope, so the INIT-internal variables are
     in scope here. *)
  let merge_init_seeds =
    NM.fold (fun mnid mnode acc ->
      match mnode with
      | Simple (_, MERGE, _, _, _) ->
          (match ES.fold (fun ((sn, sp), (dn, dp), _) a ->
             if dn = mnid && dp = 1 then Some (sn, sp) else a) loop_gr.eset None with
           | Some (sn, sp) when sn = init_nid ->
               (match get_sub_out_expr init_gid init_nid init_gr e_init sp with
                | Some rhs ->
                    let lhs = get_expr env_loop sub_gid mnid 0 `Out in
                    acc @ [ C.Expr (C.BinOp (C.Assign, lhs, rhs)) ]
                | None -> acc)
           | _ -> acc)
      | _ -> acc
    ) loop_gr.nmap []
  in
  let test_nid, test_gr = match find_subgraph loop_gr "TEST" with | Some x -> x | _ -> failwith "no TEST" in
  let test_gid = try GidMap.find (sub_gid, test_nid) env.gid_table with _ -> -1 in
  (* Run TEST once (outside while) to get cond expression and pre-declare its vars *)
  let env_test1 = { env_loop with parent_env = Some env_loop; curr_gid = test_gid; curr_gr = test_gr; parent_map = IntMap.add test_gid (sub_gid, test_nid) env_loop.parent_map } in
  let test_stmts1, e_test1 = lower_graph env_test1 loop_gr test_nid test_gr test_gid in
  let cond = match ES.fold (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc) test_gr.eset None with
    | Some (sn, sp) -> get_expr e_test1 test_gid sn sp `Out
    | None -> C.LitInt 0 in
  let env_loop = { env_loop with var_map = e_test1.var_map; type_table = e_test1.type_table; seen_decls = e_test1.seen_decls } in
  let body_nid, body_gr = match find_subgraph loop_gr "BODY" with | Some x -> x | _ -> failwith "no BODY" in
  let body_gid = try GidMap.find (sub_gid, body_nid) env.gid_table with _ -> -1 in
  let env_body = { env_loop with parent_env = Some env_loop; curr_gid = body_gid; curr_gr = body_gr; parent_map = IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map } in
  let body_stmts, e_body = lower_graph env_body loop_gr body_nid body_gr body_gid in
  let env_loop = { env_loop with var_map = e_body.var_map; type_table = e_body.type_table; seen_decls = e_body.seen_decls } in
  (* Capture BODY boundary outputs into loop-scope variables.
     The body-internal C variable is declared inside the while {} block, so it is out of
     scope for consumers that run after the loop (RETURNS) or at loop level (the MERGE
     feedback). Materialize one loop-scope capture variable per BODY boundary output,
     declared at the top of the for-initial scope and assigned at the bottom of the body.
     BODY often exposes the same internal value on several boundary ports (fanout); memoize
     by the body-internal source port (sn,sp) and reuse the same capture — warn on reuse.
     Bindings are recorded only against the body graph's port keys; we never reach a parent
     scope for a name. *)
  let body_capture_decls, body_capture_assigns, env_loop =
    let memo = Hashtbl.create 8 in
    ES.fold (fun ((sn, sp), (dn, dp), _) (decls, assigns, e) ->
      (* Capture every body boundary output (dn = 0), including pass-throughs sourced
         from the body's boundary input (sn = 0). Capturing pass-throughs too guarantees
         that every MERGE backedge source is a snapshot, never a live MERGE variable. *)
      if dn = 0 then
        match Hashtbl.find_opt memo (sn, sp) with
        | Some cap_id ->
            Printf.eprintf
              "warning: lower_for_initial: BODY boundary out port %d duplicates source (%d,%d) at gid=%d; reusing memoized capture\n"
              dp sn sp sub_gid;
            (decls, assigns,
             { e with var_map = FullPortMap.add (sub_gid, body_nid, dp, `Out) cap_id e.var_map })
        | None ->
            (match FullPortMap.find_opt (body_gid, sn, sp, `Out) e_body.var_map with
             | Some src_expr ->
                 let cap_name = Printf.sprintf "v_%s_bodycap_n%d_p%d"
                   (scope_of env.gid_name_map sub_gid) sn sp in
                 let cap_id = C.Id cap_name in
                 let ty = get_final_ty e body_gid sn sp `Out in
                 let init_val = if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}") else Some (C.LitInt 0) in
                 Hashtbl.add memo (sn, sp) cap_id;
                 (decls @ [ C.Decl (ty, cap_name, init_val) ],
                  assigns @ [ C.Expr (C.BinOp (C.Assign, cap_id, src_expr)) ],
                  { e with
                    seen_decls = StringSet.add cap_name e.seen_decls;
                    var_map = FullPortMap.add (sub_gid, body_nid, dp, `Out) cap_id e.var_map;
                    type_table = FullPortMap.add (sub_gid, body_nid, dp, `Out) ty e.type_table })
             | None -> (decls, assigns, e))
      else (decls, assigns, e)
    ) body_gr.eset ([], [], env_loop)
  in
  (* Backedge copies for the loop-carried MERGE phis. Each MERGE takes its body feedback on
     input port 2; copy that into the MERGE variable at the bottom of the loop body, after
     the body captures. Every RHS resolves to a loop-scope bodycap capture, a snapshot
     distinct from any MERGE variable, so these copies cannot read a value another copy is
     about to overwrite: no SSA swap / lost-copy hazard, independent of copy order. *)
  let merge_backedge_copies =
    NM.fold (fun mnid mnode acc ->
      match mnode with
      | Simple (_, MERGE, _, _, _) ->
          (match ES.fold (fun ((sn, sp), (dn, dp), _) a ->
             if dn = mnid && dp = 2 then Some (sn, sp) else a) loop_gr.eset None with
           | Some (sn, sp) ->
               let lhs = get_expr env_loop sub_gid mnid 0 `Out in
               let rhs = get_expr env_loop sub_gid sn sp `Out in
               acc @ [ C.Expr (C.BinOp (C.Assign, lhs, rhs)) ]
           | None -> acc)
      | _ -> acc
    ) loop_gr.nmap []
  in
  (* Bug 5: after BODY, update carry-slot C variables from BODY outputs *)
  let carry_update_stmts, env_loop =
    update_carry_slots body_nid body_gid body_gr e_body env_loop
  in
  (* Run TEST a second time inside the while body.  Its variables are already
     pre-declared (in seen_decls from the first run), so only assignments are
     emitted — no duplicate declarations in C. *)
  let env_test2 = { env_loop with parent_env = Some env_loop; curr_gid = test_gid; curr_gr = test_gr; parent_map = IntMap.add test_gid (sub_gid, test_nid) env_loop.parent_map } in
  let test_stmts2, e_test2 = lower_graph env_test2 loop_gr test_nid test_gr test_gid in
  let env_loop = { env_loop with var_map = e_test2.var_map; type_table = e_test2.type_table; seen_decls = e_test2.seen_decls } in
  let while_loop = C.While (cond, body_stmts @ body_capture_assigns @ merge_backedge_copies @ carry_update_stmts @ test_stmts2) in
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
    | None ->
        (* Trace via ret_gr eset to find source of boundary input dp *)
        (match ES.fold (fun ((sn, sp), (dn, dp2), _) a ->
           if dn = 0 && dp2 = dp then Some (sn, sp) else a) ret_gr.eset None with
         | Some (sn, sp) ->
             (match FullPortMap.find_opt (ret_gid, sn, sp, `Out) e_ret.var_map with
              | Some src_expr ->
                  let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
                  (acc @ stmts, e')
              | None -> (acc, e))
         | None -> (acc, e))
  ) ([], { e_ret with curr_gid = gid; curr_gr = gr }) out_pids in
  (decl_stmts @ [ C.Compound (loop_local_decls @ merge_decls @ body_capture_decls @ loop_in_stmts @ init_stmts @ carry_init_stmts @ merge_init_seeds @ test_stmts1 @ [ while_loop ] @ ret_stmts @ props) ], final_env)

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
