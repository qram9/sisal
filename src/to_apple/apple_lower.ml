(** apple_lower.ml: The "Apple Lowering" pass for Sisal. This module implements
    the complex logic of translating dataflow IF1 graphs into imperative C-AST
    nodes, with specific optimizations for Apple Silicon (GCD for parallelism,
    Accelerate framework for vector ops). *)

open Ir.If1
open Apple_env
open Apple_helpers

(** [c_op_of_node_sym sym] maps a basic IF1 node symbol to a C binary operator. *)
let c_op_of_node_sym = function
  | ADD -> Some C.Add
  | SUBTRACT -> Some C.Sub
  | TIMES -> Some C.Mul
  | EQUAL -> Some C.Eq
  | GREATER -> Some C.Gt
  | GREATER_EQUAL -> Some C.Ge
  | LESSER -> Some C.Lt
  | LESSER_EQUAL -> Some C.Le
  | _ -> None

(** [intrinsic_name_of_node_sym sym] maps special IF1 symbols to runtime helper
    function names. *)
let intrinsic_name_of_node_sym = function
  | "_SABS__F__F" -> Some "fabsf"
  | "_SABS__D__D" -> Some "fabs"
  | "_SABS__I__I" -> Some "abs"
  | "_SSQRT__F__F" -> Some "sqrtf"
  | "_SSQRT__D__D" -> Some "sqrt"
  | "_SEXP__F__F" -> Some "expf"
  | "_SEXP__D__D" -> Some "exp"
  | "_SLOG__F__F" -> Some "logf"
  | "_SLOG__D__D" -> Some "log"
  | "_SSIN__F__F" -> Some "sinf"
  | "_SSIN__D__D" -> Some "sin"
  | "_SCOS__F__F" -> Some "cosf"
  | "_SCOS__D__D" -> Some "cos"
  | "_STAN__F__F" -> Some "tanf"
  | "_STAN__D__D" -> Some "tan"
  | "_SMAX__FF__F" -> Some "fmaxf"
  | "_SMAX__DD__D" -> Some "fmax"
  | "_SMIN__FF__F" -> Some "fminf"
  | "_SMIN__DD__D" -> Some "fmin"
  | "_SFLOOR__F__F" -> Some "floorf"
  | "_SFLOOR__D__D" -> Some "floor"
  | "_SCEIL__F__F" -> Some "ceilf"
  | "_SCEIL__D__D" -> Some "ceil"
  | "_STRUNC__F__I" -> Some "(int32_t)truncf"
  | "_STRUNC__D__L" -> Some "(int64_t)trunc"
  | "_STRUNC__H__S" -> Some "(int16_t)truncf"
  | "_SRADIANS__F__F" -> Some "sisal_radians_f"
  | "_SRADIANS__D__D" -> Some "sisal_radians_d"
  | "_SDEGREES__F__F" -> Some "sisal_degrees_f"
  | "_SDEGREES__D__D" -> Some "sisal_degrees_d"
  | _ -> None

let get_expr_unsafe env g n p dir =
  match get_expr env g n p dir with
  | Some e -> e
  | None -> C.Id (var_name env env.curr_gr g n p dir)

(** [lower_graph env gr gid] translates an IF1 graph into a list of C statements.
    Uses the edge set exclusively for boundary input resolution via
    [compound_nid_in_parent] in the env. *)
let rec lower_graph env gr gid =
  assert_compound_boundary_types gr;
  let fanout_counts, mandatory_ports = compute_fanout gr in
  let env = { env with curr_gid = gid; curr_gr = gr; fanout_map = fanout_counts; mandatory_ports } in

  (* 1. Populate preds from local edges. *)
  let preds = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    FullPortMap.add (gid, dn, dp, `In) (gid, sn, sp, `Out) m)
    gr.eset env.preds in
  let env = { env with preds } in

  let _cs, _ps = gr.symtab in

  (* 2. Materialise boundary inputs using names from cs where available. *)
  let b_in_pids_all =
    ES.fold (fun ((sn, sp), _, _) acc -> if sn = 0 then IntSet.add sp acc else acc)
      gr.eset IntSet.empty |> IntSet.elements in
  let b_in_decls, env =
    List.fold_left (fun (decls, e) p ->
      if FullPortMap.mem (gid, 0, p, `Out) e.var_map || gid = 0 then (decls, e)
      else
        let v_o = var_name e gr gid 0 p `Out in
        if StringSet.mem v_o e.seen_decls then (decls, e)
        else
          match e.parent_env with
          | Some p_env ->
              let cid = e.compound_nid_in_parent in
              let feeding = all_edges_ending_at_port cid p p_env.curr_gr in
              (match ES.choose_opt feeding with
               | Some ((src_n, src_p), _, _) ->
                   (match get_expr p_env p_env.curr_gid src_n src_p `Out with
                    | Some src_expr ->
                        let ty = get_port_type e gr 0 p `Out in
                        let e' = { e with
                          seen_decls = StringSet.add v_o e.seen_decls;
                          var_map = FullPortMap.add (gid, 0, p, `Out) (C.Id v_o) e.var_map } in
                        (decls @ [ C.Decl (ty, v_o, Some src_expr) ], e')
                    | None -> (decls, e))
               | None -> (decls, e))
          | None -> (decls, e)
    ) ([], env) b_in_pids_all
  in

  (* 3. Computation in topological order. *)
  let res_stmts, env =
    let sorted_nodes = topo_sort gr in
    List.fold_left (fun (acc_stmts, e) nid ->
      if nid = 0 then (acc_stmts, e)
      else match NM.find_opt nid gr.nmap with
      | Some (Literal (_, code, value, _)) ->
          let v_res = var_name e gr gid nid 0 `Out in
          if StringSet.mem v_res e.seen_decls then (acc_stmts, e)
          else
            let ty = get_port_type e gr nid 0 `Out in
            let lit = try match code with
              | REAL | DOUBLE -> C.LitFloat (float_of_string value)
              | BOOLEAN -> C.Id (String.lowercase_ascii value)
              | _ -> C.LitInt (int_of_string value)
              with _ -> C.LitInt 0 in
            let e' = { e with
              seen_decls = StringSet.add v_res e.seen_decls;
              var_map = FullPortMap.add (gid, nid, 0, `Out) (C.Id v_res) e.var_map } in
            (acc_stmts @ [ C.Comment (Printf.sprintf "#%d Literal(%s)" nid value); C.Decl (ty, v_res, Some lit) ], e')
      | Some node ->
          let v_res = var_name e gr gid nid 0 `Out in
          let decl, e = if StringSet.mem v_res e.seen_decls then ([], e)
            else
              let ty = get_port_type e gr nid 0 `Out in
              ([ C.Decl (ty, v_res, None) ],
               { e with
                 seen_decls = StringSet.add v_res e.seen_decls;
                 var_map = FullPortMap.add (gid, nid, 0, `Out) (C.Id v_res) e.var_map }) in
          (* Declare all output ports > 0 for multi-output nodes (e.g. LET returning tuple). *)
          let extra_out_ports =
            ES.fold (fun ((sn, sp), _, _) acc ->
              if sn = nid && sp > 0 then IntSet.add sp acc else acc)
              gr.eset IntSet.empty |> IntSet.elements in
          let extra_decls, e = List.fold_left (fun (ds, ev) sp ->
            let v_sp = match get_port_name_from_cs gr nid sp `Out with
                       | Some n -> n | None -> var_name ev gr gid nid sp `Out in
            if StringSet.mem v_sp ev.seen_decls then (ds, ev)
            else
              let ty = get_port_type ev gr nid sp `Out in
              (ds @ [ C.Decl (ty, v_sp, None) ],
               { ev with
                 seen_decls = StringSet.add v_sp ev.seen_decls;
                 var_map = FullPortMap.add (gid, nid, sp, `Out) (C.Id v_sp) ev.var_map })
          ) ([], e) extra_out_ports in
          let e = ES.fold (fun ((sn, sp), (dn, dp), _) ev ->
            if dn = nid then
              match get_expr ev gid sn sp `Out with
              | Some src -> { ev with var_map = FullPortMap.add (gid, dn, dp, `In) src ev.var_map }
              | None -> ev
            else ev) gr.eset e in
          let node_stmts, e' = lower_node e gr nid node in
          let node_comment = match node with
            | Simple (_, sym, _, _, _) -> Printf.sprintf "#%d %s" nid (string_of_node_sym sym)
            | Compound (_, _, _, pr, _, _) ->
                let label = List.find_map (function Name n -> Some n | _ -> None) pr
                            |> Option.value ~default:"Compound" in
                Printf.sprintf "#%d %s" nid label
            | _ -> Printf.sprintf "#%d" nid in
          (acc_stmts @ [ C.Comment node_comment ] @ decl @ extra_decls @ node_stmts, e')
      | None -> (acc_stmts, e)
    ) ([], env) sorted_nodes
  in

  (* 4. Boundary outputs: declare a named variable and assign from inner computation. *)
  let b_outs_pids =
    ES.fold (fun (_, (dn, dp), _) acc ->
      if dn = 0 then IntSet.add dp acc else acc)
      gr.eset IntSet.empty
    |> IntSet.elements
  in

  let b_out_decls, propagation, final_env =
    List.fold_left (fun (decls, props, e) pid ->
      let v_i = var_name e gr gid 0 pid `In in
      match get_expr e gid 0 pid `In with
      | Some src_expr ->
          if src_expr = C.Id v_i then (decls, props, e)
          else
            let ty = get_port_type e gr 0 pid `In in
            let decl = if StringSet.mem v_i e.seen_decls then []
                       else [ C.Decl (ty, v_i, None) ] in
            let e' = { e with
              var_map = FullPortMap.add (gid, 0, pid, `In) (C.Id v_i) e.var_map;
              seen_decls = if decl <> [] then StringSet.add v_i e.seen_decls
                           else e.seen_decls } in
            let prop = [ C.Expr (C.BinOp (C.Assign, C.Id v_i, src_expr)) ] in
            (decls @ decl, props @ prop, e')
      | None -> (decls, props, e))
    ([], [], env) b_outs_pids
  in

  (b_in_decls @ res_stmts @ b_out_decls @ propagation, final_env)

and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, _ty, pr, loop_gr, _) ->
      let sub_gid = alloc_gid env.gid_table gid cid in
      let is_real_forall = sy = INTERNAL &&
        List.exists (function Name n -> n = "FORALL" | _ -> false) pr in
      if is_real_forall then
        lower_forall env gr gid nid cid loop_gr sub_gid pr
      else if Option.is_some (find_subgraph loop_gr "PREDICATE") then
        lower_if_graph env gr cid loop_gr sub_gid
      else begin
        let env_child = { env with
          curr_gid = sub_gid;
          curr_gr = loop_gr;
          parent_env = Some env;
          compound_nid_in_parent = cid } in
        let body, env_after = lower_graph env_child loop_gr sub_gid in
        let results = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
          if sn = cid then (sp, dp) :: acc else acc) gr.eset [] in
        let result_propagation = List.filter_map (fun (sp, dp) ->
          match get_expr env_after sub_gid 0 sp `In with
          | Some src ->
              let dst = get_expr_unsafe env gid cid sp `Out in
              if src = dst then None
              else Some (C.Expr (C.BinOp (C.Assign, dst, src)))
          | None -> None) results in
        (body @ result_propagation,
         { env_after with curr_gid = gid; curr_gr = gr; parent_env = env.parent_env })
      end
  | Simple (_, sym, pin, pout, pr) -> lower_simple env gr nid sym pin pout pr
  | Literal _ -> ([], env)
  | _ -> ([], env)

and lower_simple env gr nid sym _pin _pout _pr =
  let gid = env.curr_gid in
  let e1 = try get_expr_unsafe env gid nid 0 `In with _ -> C.LitInt 0 in
  let e2 = try get_expr_unsafe env gid nid 1 `In with _ -> C.LitInt 0 in
  let v_res = get_expr_unsafe env gid nid 0 `Out in
  match sym with
  | ADD    -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Add, e1, e2))) ], env)
  | SUBTRACT -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Sub, e1, e2))) ], env)
  | TIMES  -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Mul, e1, e2))) ], env)
  | EQUAL  -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Eq,  e1, e2))) ], env)
  | GREATER -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Gt, e1, e2))) ], env)
  | GREATER_EQUAL -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Ge, e1, e2))) ], env)
  | LESSER -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Lt, e1, e2))) ], env)
  | LESSER_EQUAL -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Le, e1, e2))) ], env)
  | DV_NUM_RANK ->
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Member (e1, "rank"))) ], env)
  | AELEMENT | DV_ELEMENT | DV_LOAD_LINEAR ->
      let cast_ptr = C.Cast (C.Pointer (C.Basic "double", []), C.Member (e1, "data")) in
      let idx = if sym = DV_LOAD_LINEAR then e2
                else C.BinOp (C.Sub, e2, C.Member (e1, "lower_bound")) in
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Index (cast_ptr, idx))) ], env)
  | DV_OFFSET_AT ->
      ([ C.Expr (C.BinOp (C.Assign, v_res, e2)) ], env)
  | RANGEGEN ->
      (* count = hi - lo + 1; port 0 = lo, port 1 = hi *)
      let count = C.BinOp (C.Add, C.BinOp (C.Sub, e2, e1), C.LitInt 1) in
      ([ C.Expr (C.BinOp (C.Assign, v_res, count)) ], env)
  | ASIZE ->
      ([ C.Expr (C.BinOp (C.Assign, v_res,
           C.Cast (C.Basic "int32_t", C.Member (e1, "size")))) ], env)
  | ALIML ->
      ([ C.Expr (C.BinOp (C.Assign, v_res,
           C.Cast (C.Basic "int32_t", C.Member (e1, "lower_bound")))) ], env)
  | ALIMH ->
      (* upper_bound = lower_bound + size - 1 *)
      let ub = C.BinOp (C.Sub,
        C.BinOp (C.Add, C.Member (e1, "lower_bound"),
          C.Cast (C.Basic "int64_t", C.Member (e1, "size"))),
        C.LitInt 1) in
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Cast (C.Basic "int32_t", ub))) ], env)
  | ASETL ->
      (* Return array with updated lower_bound *)
      let copy = C.Expr (C.BinOp (C.Assign, v_res, e1)) in
      let set_lb = C.Expr (C.BinOp (C.Assign, C.Member (v_res, "lower_bound"), e2)) in
      ([ copy; set_lb ], env)
  | DV_DIMENSION ->
      (* DV_DIMENSION(A, k): for 1D arrays, returns size of dimension k *)
      ([ C.Expr (C.BinOp (C.Assign, v_res,
           C.Cast (C.Basic "int32_t", C.Member (e1, "size")))) ], env)
  | RELEMENTS ->
      (* RELEMENTS(_, dim_result): extracts element count from DV_DIMENSION result *)
      ([ C.Expr (C.BinOp (C.Assign, v_res, e2)) ], env)
  | DV_RESHAPE_BY_SHAPE ->
      (* DV_RESHAPE_BY_SHAPE(A, shape): for 1D, identity *)
      ([ C.Expr (C.BinOp (C.Assign, v_res, e1)) ], env)
  | OR ->
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.LogOr, e1, e2))) ], env)
  | AND ->
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.LogAnd, e1, e2))) ], env)
  | NOT ->
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.UnaryOp (C.LogNot, e1))) ], env)
  | NEGATE ->
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.UnaryOp (C.Negate, e1))) ], env)
  | TYPECAST ->
      let out_ty = get_port_type env gr nid 0 `Out in
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Cast (out_ty, e1))) ], env)
  | REDUCE_ALL ->
      let fname = List.find_map (function Name n -> Some n | _ -> None) _pr
                  |> Option.value ~default:"sum" in
      let out_ty = get_port_type env gr nid 0 `Out in
      let reduce_fn = match (String.lowercase_ascii fname, out_ty) with
        | ("sum", C.Basic "double") -> "sisal_array_reduce_double_sum"
        | ("sum", C.Basic "float")  -> "sisal_array_reduce_sum"
        | ("sum", C.Basic "int32_t") -> "sisal_array_reduce_int_sum"
        | ("product", C.Basic "double") -> "sisal_array_reduce_double_product"
        | ("product", C.Basic "float")  -> "sisal_array_reduce_product"
        | ("product", C.Basic "int32_t") -> "sisal_array_reduce_int_product"
        | ("least", C.Basic "double")   -> "sisal_array_reduce_double_least"
        | ("least", C.Basic "float")    -> "sisal_array_reduce_least"
        | ("least", C.Basic "int32_t")   -> "sisal_array_reduce_int_least"
        | ("greatest", C.Basic "double") -> "sisal_array_reduce_double_greatest"
        | ("greatest", C.Basic "float")  -> "sisal_array_reduce_greatest"
        | ("greatest", C.Basic "int32_t") -> "sisal_array_reduce_int_greatest"
        | _ -> "sisal_array_reduce_double_sum"
      in
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Call (reduce_fn, [e1]))) ], env)
  | INVOCATION ->
      let fname = List.find_map (function Name n -> Some n | _ -> None) _pr
                  |> Option.value ~default:"unknown_fn" in
      let in_ports =
        ES.fold (fun (_, (dn, dp), _) acc ->
          if dn = nid then IntSet.add dp acc else acc)
          gr.eset IntSet.empty |> IntSet.elements in
      let args = List.filter_map (fun pid ->
        get_expr env gid nid pid `In) in_ports in
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Call (fname, args))) ], env)
  | _ -> ([], env)

(** [lower_if_graph env parent_gr cid loop_gr loop_gid] lowers an IF compound.
    Creates an intermediate env_loop so that PREDICATE/THEN/ELSE boundary inputs
    resolve against loop_gr's edges, not the outer function graph. *)
and lower_if_graph env parent_gr cid loop_gr loop_gid =
  let gid = env.curr_gid in
  (* Intermediate env for loop_gr: its parent is the outer function scope. *)
  let loop_preds = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    FullPortMap.add (loop_gid, dn, dp, `In) (loop_gid, sn, sp, `Out) m)
    loop_gr.eset env.preds in
  let env_loop = { env with
    curr_gid = loop_gid;
    curr_gr = loop_gr;
    preds = loop_preds;
    parent_env = Some env;
    compound_nid_in_parent = cid } in

  let pred_cid, pred_sg =
    match find_subgraph loop_gr "PREDICATE" with
    | Some x -> x | _ -> failwith "lower_if_graph: no PREDICATE" in
  let pgid = alloc_gid env.gid_table loop_gid pred_cid in
  let env_pred = { env_loop with
    curr_gid = pgid; curr_gr = pred_sg;
    parent_env = Some env_loop;
    compound_nid_in_parent = pred_cid } in
  let pred_stmts, e_after = lower_graph env_pred pred_sg pgid in
  let v_pred = get_expr_unsafe e_after pgid 0 0 `In in

  let then_cid, then_sg =
    match find_subgraph loop_gr "THEN" with
    | Some x -> x | _ -> failwith "lower_if_graph: no THEN" in
  let tgid = alloc_gid env.gid_table loop_gid then_cid in
  let env_then = { env_loop with
    curr_gid = tgid; curr_gr = then_sg;
    parent_env = Some env_loop;
    compound_nid_in_parent = then_cid;
    seen_decls = e_after.seen_decls } in
  let then_body, e_then = lower_graph env_then then_sg tgid in
  let then_prop = C.Expr (C.BinOp (C.Assign,
    get_expr_unsafe env gid cid 0 `Out,
    get_expr_unsafe e_then tgid 0 0 `In)) in

  let else_cid, else_sg =
    match find_subgraph loop_gr "ELSE" with
    | Some x -> x | _ -> failwith "lower_if_graph: no ELSE" in
  let egid = alloc_gid env.gid_table loop_gid else_cid in
  let env_else = { env_loop with
    curr_gid = egid; curr_gr = else_sg;
    parent_env = Some env_loop;
    compound_nid_in_parent = else_cid;
    seen_decls = e_after.seen_decls } in
  let else_body, e_else = lower_graph env_else else_sg egid in
  let else_prop = C.Expr (C.BinOp (C.Assign,
    get_expr_unsafe env gid cid 0 `Out,
    get_expr_unsafe e_else egid 0 0 `In)) in

  (* Propagate IF outputs back to parent scope. *)
  let if_out_pids =
    ES.fold (fun ((sn, sp), _, _) acc ->
      if sn = cid then IntSet.add sp acc else acc)
      parent_gr.eset IntSet.empty
    |> IntSet.elements in
  let if_out_props = List.filter_map (fun sp ->
    match get_expr e_then tgid 0 sp `In with
    | Some _ ->
        let dst = get_expr_unsafe env gid cid sp `Out in
        let src_then = get_expr_unsafe e_then tgid 0 sp `In in
        let src_else = get_expr_unsafe e_else egid 0 sp `In in
        Some (sp, dst, src_then, src_else)
    | None -> None) if_out_pids in
  let then_props = List.filter_map (fun (_, dst, src, _) ->
    if src = dst then None else Some (C.Expr (C.BinOp (C.Assign, dst, src))))
    if_out_props in
  let else_props = List.filter_map (fun (_, dst, _, src) ->
    if src = dst then None else Some (C.Expr (C.BinOp (C.Assign, dst, src))))
    if_out_props in

  let seen = StringSet.union e_then.seen_decls e_else.seen_decls in
  let then_full = then_body @ (if then_props <> [] then then_props else [then_prop]) in
  let else_full = else_body @ (if else_props <> [] then else_props else [else_prop]) in
  (pred_stmts @ [ C.If (v_pred, then_full, else_full) ],
   { e_after with seen_decls = seen;
                  curr_gid = gid;
                  curr_gr = parent_gr;
                  parent_env = env.parent_env })

(** [lower_forall env gr gid nid cid loop_gr sub_gid pr] lowers a FORALL compound.
    Creates env_loop for loop_gr so GENERATOR/BODY boundary inputs resolve
    against loop_gr's edges. *)
and lower_forall env gr gid nid cid loop_gr sub_gid pr =
  let _ = cid in
  (* Intermediate env for loop_gr. *)
  let loop_preds = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    FullPortMap.add (sub_gid, dn, dp, `In) (sub_gid, sn, sp, `Out) m)
    loop_gr.eset env.preds in
  let env_loop = { env with
    curr_gid = sub_gid;
    curr_gr = loop_gr;
    preds = loop_preds;
    parent_env = Some env;
    compound_nid_in_parent = nid } in

  let gen_info  = find_subgraph loop_gr "GENERATOR" in
  let body_info = find_subgraph loop_gr "BODY" in
  match (gen_info, body_info) with
  | Some (gen_nid, gen_gr), Some (body_nid, body_gr) ->
      let gen_gid = alloc_gid env.gid_table sub_gid gen_nid in
      let env_gen = { env_loop with
        curr_gid = gen_gid; curr_gr = gen_gr;
        parent_env = Some env_loop;
        compound_nid_in_parent = gen_nid } in
      let gen_stmts, e_gen = lower_graph env_gen gen_gr gen_gid in
      let count  = get_expr_unsafe e_gen gen_gid 0 0 `In in
      let res_v  = get_expr_unsafe env gid nid 0 `Out in
      let alloc  = C.Expr (C.BinOp (C.Assign, res_v,
        C.Call ("sisal_array_alloc_empty",
          [ C.LitInt 1; C.LitInt 0; C.Cast (C.Basic "uint64_t", count) ]))) in
      let body_gid = alloc_gid env.gid_table sub_gid body_nid in
      let loop_idx_var = Printf.sprintf "idx_g%d_n%d" body_gid body_nid in
      (* Find RANGEGEN's lower bound so LFI = lo + idx (Sisal ranges are lo-based).
         For 0-based ranges (lo=0 or ALIML=0), this is a no-op. *)
      let rangegen_lo_expr =
        NM.fold (fun rg_nid node acc ->
          match acc with Some _ -> acc
          | None ->
            (match node with
             | Simple (_, RANGEGEN, _, _, _) -> get_expr e_gen gen_gid rg_nid 0 `In
             | _ -> None))
          gen_gr.nmap None
      in
      (* Enrich env_loop so BODY can resolve its boundary inputs via edge-set.
         (1) Add GENERATOR output so BODY's "count" port resolves correctly.
         (2) Pre-populate __LFI (the loop iterator) in loop_gr boundary so that
             BODY's __LFI boundary port resolves to (lo + idx_var) via edge-set. *)
      let env_loop =
        let vm = FullPortMap.add (sub_gid, gen_nid, 0, `Out) count env_loop.var_map in
        let cs, ps = loop_gr.symtab in
        (* Find loop index boundary port in loop_gr.
           Strategy 1: look in cs for any boundary input (val_def=0) named "__LFI*".
           Strategy 2: find the variable defined by gen_nid in ps, then look up in cs.
           Strategy 1 takes priority to avoid false positives when ps has coincidental val_def matches. *)
        let lfi_opt =
          let find_named_lfi m =
            SM.fold (fun name entry acc ->
              if acc <> None then acc
              else if entry.val_def = 0 &&
                      (sanitize name = "__LFI" ||
                       String.starts_with ~prefix:"__LFI" (sanitize name)) then
                Some entry.def_port
              else acc) m None in
          match find_named_lfi cs with
          | Some _ as p -> p
          | None ->
              (* Fallback: find the var defined by gen_nid in ps, then look up its boundary port in cs. *)
              let gen_var_name = SM.fold (fun name entry acc ->
                if acc <> None then acc
                else if entry.val_def = gen_nid && entry.def_port = 0 then Some name
                else acc) ps None in
              (match gen_var_name with
               | Some vname ->
                   (match SM.find_opt vname cs with
                    | Some e when e.val_def = 0 -> Some e.def_port
                    | _ -> None)
               | None -> None)
        in
        let lfi_val =
          match rangegen_lo_expr with
          | None | Some (C.LitInt 0) -> C.Id loop_idx_var
          | Some lo -> C.BinOp (C.Add, C.Id loop_idx_var, lo)
        in
        let vm = match lfi_opt with
          | Some lfi_p -> FullPortMap.add (sub_gid, 0, lfi_p, `Out) lfi_val vm
          | None -> vm in
        { env_loop with var_map = vm; seen_decls = e_gen.seen_decls } in
      let env_body = { env_loop with
        curr_gid = body_gid; curr_gr = body_gr;
        parent_env = Some env_loop;
        compound_nid_in_parent = body_nid;
        seen_decls = StringSet.add loop_idx_var env_loop.seen_decls;
        var_map = env_loop.var_map } in
      let body_stmts, e_body = lower_graph env_body body_gr body_gid in
      let out_ty = get_port_type e_body body_gr 0 0 `In in
      let store = C.Expr (C.BinOp (C.Assign,
        C.Index (C.Cast (C.Pointer (out_ty, []), C.Member (res_v, "data")),
                 C.Id loop_idx_var),
        get_expr_unsafe e_body body_gid 0 0 `In)) in
      let loop = C.For (
        C.Decl (C.Basic "int32_t", loop_idx_var, Some (C.LitInt 0)),
        C.BinOp (C.Lt, C.Id loop_idx_var, count),
        C.BinOp (C.Assign, C.Id loop_idx_var,
                 C.BinOp (C.Add, C.Id loop_idx_var, C.LitInt 1)),
        body_stmts @ [ store ]) in

      (* Result propagation: assign child boundary outputs to parent node outputs. *)
      let out_pids = ES.fold (fun ((sn, sp), _, _) acc ->
        if sn = cid then IntSet.add sp acc else acc) gr.eset IntSet.empty
        |> IntSet.elements in
      let props, env = List.fold_left (fun (ps, e) sp ->
        if sp = 0 then
          let dst = get_expr_unsafe env gid cid 0 `Out in
          if dst = res_v then (ps, e)
          else (ps @ [ C.Expr (C.BinOp (C.Assign, dst, res_v)) ], e)
        else
          match get_expr e_body body_gid 0 sp `In with
          | Some src ->
              let dst = get_expr_unsafe env gid cid sp `Out in
              if src = dst then (ps, e)
              else
                (* Ensure 'src' (child boundary var) is declared in parent if not already. *)
                let src_decl, e' = match src with
                  | C.Id name when not (StringSet.mem name e.seen_decls) ->
                      let ty = get_port_type e_body body_gr 0 sp `In in
                      ([ C.Decl (ty, name, None) ], { e with seen_decls = StringSet.add name e.seen_decls })
                  | _ -> ([], e) in
                (ps @ src_decl @ [ C.Expr (C.BinOp (C.Assign, dst, src)) ], e')
          | None -> (ps, e)) ([], env) out_pids in

      (gen_stmts @ [ alloc; loop ] @ props,
       { env with seen_decls = env.seen_decls })

  | _ -> ([], env)

and lower_for_initial _env _gr _gid _nid _cid _loop_gr _sub_gid _var_map_child =
  ([], _env)

let lower_procedure tm _nid node =
  match node with
  | Compound (_, INTERNAL, _ty, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name nm -> Some nm | _ -> None) pr
        |> Option.value ~default:"unnamed_proc" in
      let sub_gid = 0 in
      let gid_table = build_gid_table sub_gr in
      (* Function parameters: use edge set only (in_port_list is unreliable). *)
      let all_b_ins =
        ES.fold (fun ((sn, sp), _, _) acc ->
          if sn = 0 then IntSet.add sp acc else acc)
          sub_gr.eset IntSet.empty
        |> IntSet.elements in
      let dummy_env = {
        tm;
        var_map = FullPortMap.empty;
        preds = FullPortMap.empty;
        curr_gid = 0;
        curr_gr = sub_gr;
        parent_env = None;
        compound_nid_in_parent = 0;
        seen_decls = StringSet.empty;
        fanout_map = PortFanout.empty;
        mandatory_ports = PortSet.empty;
        gid_table;
        force_gpu = false } in
      let params =
        List.map (fun pid ->
          let ty = get_port_type dummy_env sub_gr 0 pid `Out in
          let name = match get_port_name_from_cs sub_gr 0 pid `Out with
                     | Some n -> n | None -> var_name dummy_env sub_gr 0 0 pid `Out in
          (ty, name))
          all_b_ins in
      let var_map =
        List.fold_left2 (fun m pid (_, name) ->
          FullPortMap.add (0, 0, pid, `Out) (C.Id name) m)
          FullPortMap.empty all_b_ins params in
      let env = { dummy_env with
        var_map;
        seen_decls =
          List.fold_left (fun s (_, n) -> StringSet.add n s)
            StringSet.empty params } in
      let body, env_after = lower_graph env sub_gr sub_gid in
      let all_b_outs =
        ES.fold (fun (_, (dn, dp), _) acc ->
          if dn = 0 then IntSet.add dp acc else acc)
          sub_gr.eset IntSet.empty
        |> IntSet.elements in
      let ret_exprs =
        List.map (fun pid ->
          let res_v = get_expr_unsafe env_after sub_gid 0 pid `In in
          (pid, res_v))
          all_b_outs in
      let ret_count = List.length ret_exprs in
      if ret_count > 1 then
        let struct_name = func_name ^ "_results" in
        let fields = List.map (fun (dp, _) ->
          let ty = get_port_type env_after sub_gr 0 dp `In in
          ("res_" ^ string_of_int dp, ty)) ret_exprs in
        let res_var = "res_obj" in
        let decl = C.Decl (C.Basic ("struct " ^ struct_name), res_var, None) in
        let assigns = List.map (fun (dp, e) ->
          C.Expr (C.BinOp (C.Assign,
            C.Member (C.Id res_var, "res_" ^ string_of_int dp), e)))
          ret_exprs in
        Some ({ C.return_ty = C.Basic ("struct " ^ struct_name);
                name = func_name; params;
                body = (decl :: body) @ assigns @ [ C.Return (Some (C.Id res_var)) ];
                extern_c = true },
              Some (struct_name, fields))
      else if ret_count = 1 then
        let dp, e = List.hd ret_exprs in
        let ty = get_port_type env_after sub_gr 0 dp `In in
        Some ({ C.return_ty = ty; name = func_name; params;
                body = body @ [ C.Return (Some e) ]; extern_c = true }, None)
      else
        Some ({ C.return_ty = C.Void; name = func_name; params;
                body; extern_c = true }, None)
  | _ -> None

let translate gr =
  let _, tm, _ = gr.typemap in
  let procs =
    NM.fold (fun nid node acc ->
      match lower_procedure tm nid node with
      | Some p -> p :: acc
      | None -> acc)
      gr.nmap [] in
  let procedures, result_structs = List.split procs in
  let result_struct_decls =
    List.filter_map (function
      | Some (name, fields) -> Some (C.Type (C.Struct (name, fields)))
      | None -> None)
      result_structs in
  let record_structs =
    TM.fold (fun id ty acc ->
      match ty with
      | Record (_, _fields, _) ->
          let f_list =
            List.mapi (fun i tid ->
              ("f" ^ string_of_int i,
               c_type_of_if1_ty tm (TM.find tid tm)))
              (get_tuple_types tm id) in
          C.Type (C.Struct ("struct_rec_" ^ string_of_int id, f_list)) :: acc
      | _ -> acc)
      tm [] in
  let prototypes = List.map (fun p -> C.Prototype p) procedures in
  let globals =
    [ C.Macro "define SISAL_DEBUG" ] @
    record_structs @ result_struct_decls @ prototypes in
  { C.filename = "out.cpp";
    C.includes = [ "stdio.h"; "stdint.h"; "stdbool.h"; "iostream";
                   "dispatch/dispatch.h"; "Accelerate/Accelerate.h";
                   "sisal_runtime.h" ];
    C.globals = globals;
    C.procedures = procedures }
