open Ir.If1
open Apple_env
open Apple_helpers

let rec lower_graph env gr gid =
  let env_ref = ref { env with curr_gid = gid } in
  let agreement_body = ref [] in

  (* 1. Populate preds from local edges *)
  let preds = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    FullPortMap.add (gid, dn, dp, `In) (gid, sn, sp, `Out) m
  ) gr.eset !env_ref.preds in
  env_ref := { !env_ref with preds };

  (* 2. Map and alias boundary inputs (node 0 Out ports).
     Skip entries with empty name — those are function self-reference ports
     (FUNCTION_TYPE) that have no meaning in C lowering. *)
  begin match NM.find_opt 0 gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.iter (fun (_ty_id, pid, name) ->
          if sanitize name = "" then ()
          else begin
            let ty = get_port_type !env_ref gr 0 pid `Out in
            let local_v = var_name gid 0 pid `Out in
            let raw_src = get_expr !env_ref gid 0 pid `Out in
            (* get_expr never throws; it returns C.Id local_v when no better
               expression is found.  If the port has a meaningful name (e.g. "A",
               "MODE") that maps to a C parameter or enclosing variable, use it
               as the alias source so we don't lose the binding. *)
            let src_expr =
              let sname = sanitize name in
              if raw_src = C.Id local_v && sname <> "" && C.Id sname <> C.Id local_v
              then C.Id sname
              else raw_src
            in
            if ty = C.Basic "float" && src_expr <> C.Id local_v then
              (* Type unknown (float fallback) but value already known: alias directly,
                 don't emit a typed declaration that would break for non-float values. *)
              env_ref := { !env_ref with
                var_map = FullPortMap.add (gid, 0, pid, `Out) src_expr !env_ref.var_map }
            else if src_expr <> C.Id local_v then begin
              agreement_body := C.Decl (ty, local_v, Some src_expr) :: !agreement_body;
              env_ref := { !env_ref with
                var_map = FullPortMap.add (gid, 0, pid, `Out) (C.Id local_v) !env_ref.var_map }
            end
          end
        ) ins
    | _ -> ()
  end;

  (* Pre-declare boundary outputs (node 0 In ports).
     Use both the outs metadata list and actual incoming edges for robustness. *)
  let b_outs_from_metadata = match NM.find_opt 0 gr.nmap with
    | Some (Boundary (_, outs, _, _)) -> List.mapi (fun i _ -> i) outs
    | _ -> [] in
  let b_outs_from_edges = ES.fold (fun (_, (dn, dp), _) acc ->
    if dn = 0 then IntSet.add dp acc else acc
  ) gr.eset IntSet.empty |> IntSet.elements in
  let all_b_outs = List.sort_uniq compare (b_outs_from_metadata @ b_outs_from_edges) in

  List.iter (fun pid ->
    let local_res_v = var_name gid 0 pid `In in
    (* Skip if the caller already pre-wired this boundary-out (e.g. LET output
       redirected to an outer variable so the inner scope writes directly). *)
    if FullPortMap.mem (gid, 0, pid, `In) !env_ref.var_map then ()
    else begin
      let ty = get_port_type !env_ref gr 0 pid `In in
      agreement_body := C.Decl (ty, local_res_v, None) :: !agreement_body;
      env_ref := { !env_ref with
        var_map = FullPortMap.add (gid, 0, pid, `In) (C.Id local_res_v) !env_ref.var_map }
    end
  ) all_b_outs;

  (* 3. Computation block.
     If the graph contains a SELECT node it IS an IF compound (PREDICATE/BODY/ELSE graph).
     Delegate to lower_if_graph which emits a proper if/else, writing directly to the
     boundary-out vars pre-declared above.  Otherwise use the normal topo-sorted path. *)
  let computation_body =
    let has_select = NM.exists (fun _ n ->
      match n with Simple (_, SELECT, _, _, _) -> true | _ -> false) gr.nmap in
    if has_select && Option.is_some (find_subgraph gr "PREDICATE") then
      lower_if_graph !env_ref gr gid
    else begin
      let inner_decls = ref [] in
      let seen_decls = Hashtbl.create 16 in
      NM.iter (fun nid node ->
        if nid <> 0 then (
          let pids = match node with
            | Simple (_, _, _, pout, _) | Literal (_, _, _, pout) ->
                List.init (Array.length pout) (fun i -> i)
            | Compound (_, _, _, _, sub_gr, _) ->
                (* For FORALL, loop_gr.eset is empty; fall back to outer-graph edges *)
                let from_sub = ES.fold (fun (_, (dn, dp), _) acc ->
                  if dn = 0 then dp :: acc else acc) sub_gr.eset [] in
                if from_sub <> [] then from_sub
                else ES.fold (fun ((sn, sp), _, _) acc ->
                  if sn = nid then sp :: acc else acc) gr.eset []
            | _ -> [0]
          in
          List.iter (fun pid ->
            let v = var_name gid nid pid `Out in
            if not (Hashtbl.mem seen_decls v) then (
              Hashtbl.add seen_decls v ();
              let ty = get_port_type !env_ref gr nid pid `Out in
              inner_decls := C.Decl (ty, v, None) :: !inner_decls;
              env_ref := { !env_ref with
                var_map = FullPortMap.add (gid, nid, pid, `Out) (C.Id v) !env_ref.var_map }
            )
          ) (List.sort_uniq compare pids)
        )
      ) gr.nmap;

      let topo_sorted = topo_sort gr in
      let stmts = List.fold_left (fun acc nid ->
        if nid = 0 then acc else
        match NM.find_opt nid gr.nmap with
        | Some node ->
            let node_preds = ES.filter (fun (_, (dn, _), _) -> dn = nid) gr.eset in
            ES.iter (fun ((sn, sp), (_, dp), _) ->
              let src_expr = get_expr !env_ref gid sn sp `Out in
              env_ref := { !env_ref with
                var_map = FullPortMap.add (gid, nid, dp, `In) src_expr !env_ref.var_map }
            ) node_preds;
            acc @ lower_node !env_ref gr nid node
        | None -> acc
      ) [] topo_sorted in

      let propagation = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = 0 then
          let src = get_expr !env_ref gid sn sp `Out in
          (* Use var_map for dst: a LET compound may have redirected the
             boundary-out to a caller-supplied variable (e.g. the outer
             function's result var), so honour that mapping. *)
          let dst =
            FullPortMap.find_opt (gid, 0, dp, `In) !env_ref.var_map
            |> Option.value ~default:(C.Id (var_name gid 0 dp `In))
          in
          C.Expr (C.BinOp (C.Assign, dst, src)) :: acc
        else acc
      ) gr.eset [] in

      (List.rev !inner_decls) @ stmts @ propagation
    end
  in
  (List.rev !agreement_body) @ [C.Compound computation_body], !env_ref


and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, _ty, pr, loop_gr, _assoc) ->
      let sub_gid = alloc_gid env.gid_table env.curr_gid cid in
      let var_map_child = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
        if dn = cid then
          let expr = get_expr env gid sn sp `Out in
          FullPortMap.add (sub_gid, 0, dp, `Out) expr m
        else m
      ) gr.eset env.var_map in
      let is_real_forall =
        sy = INTERNAL && List.exists (function Name n -> n = "FORALL" | _ -> false) pr in
      let is_for_initial =
        sy = INTERNAL && List.exists (function Name n -> contains_substr (String.uppercase_ascii n) "LOOP" | _ -> false) pr in
      let is_if =
        sy = INTERNAL &&
        Option.is_some (find_subgraph loop_gr "PREDICATE") &&
        Option.is_some (find_subgraph loop_gr "BODY") &&
        Option.is_some (find_subgraph loop_gr "ELSE") in
      if is_real_forall then
        lower_forall env gr gid nid cid loop_gr sub_gid var_map_child pr
      else if is_for_initial then
        lower_for_initial env gr gid nid cid loop_gr sub_gid var_map_child
      else if is_if then
        lower_if env gr gid nid cid loop_gr sub_gid var_map_child
      else
        (* Generic transparent compound (e.g. LET_NON_REC).
           Two extra wiring steps that FORALL/IF handle via their own logic:

           1. Output redirect: for each output edge (cid:sp → outer), map the
              compound's inner boundary-out port sp to the pre-declared outer
              variable, so the inner lower_graph writes directly to it and the
              outer propagation step finds the right expr.

           2. Input fallback: if no explicit outer edges feed this compound
              (LET captures environment implicitly), wire its boundary inputs
              from the outer boundary by matching port index. *)
        let var_map_child =
          ES.fold (fun ((sn, sp), _, _) vm ->
            if sn = cid then
              FullPortMap.add (sub_gid, 0, sp, `In)
                (C.Id (var_name gid nid sp `Out)) vm
            else vm
          ) gr.eset var_map_child
        in
        let has_outer_edges =
          ES.exists (fun (_, (dn, _), _) -> dn = cid) gr.eset in
        let var_map_child =
          if not has_outer_edges then
            match NM.find_opt 0 loop_gr.nmap with
            | Some (Boundary (ins, _, _, _)) ->
                List.fold_left (fun vm (_, pid, name) ->
                  let local_ref = C.Id (var_name gid 0 pid `Out) in
                  let expr = get_expr env gid 0 pid `Out in
                  (* If the parent scope has no port for this pid (e.g. the
                     enclosing if-branch subgraph has an empty boundary), get_expr
                     returns a self-reference that is never declared.  Fall back to
                     the port name as a C identifier: GLOBAL-SYM-captured variables
                     are always C parameters/aliases already in scope. *)
                  let expr =
                    let sname = sanitize name in
                    if expr = local_ref && sname <> "" && C.Id sname <> local_ref
                    then C.Id sname
                    else expr
                  in
                  FullPortMap.add (sub_gid, 0, pid, `Out) expr vm
                ) var_map_child ins
            | _ -> var_map_child
          else var_map_child
        in
        let sub_stmts, _env_after_sub =
          lower_graph { env with var_map = var_map_child; parent_env = Some env } loop_gr sub_gid in
        [C.Compound sub_stmts]
  | Simple (_, sym, _pin, _pout, _pr) ->
      lower_simple env gr nid sym
  | Literal (_, code, value, _pout) ->
      let v_res = get_expr env gid nid 0 `Out in
      let lit = try
        match code with
        | REAL | DOUBLE -> C.LitFloat (float_of_string value)
        | BOOLEAN -> C.Id (String.lowercase_ascii value)
        | _ -> C.LitInt (int_of_string value)
      with _ -> C.LitInt 0 in
      [C.Expr (C.BinOp (C.Assign, v_res, lit))]
  | _ -> []

and lower_simple env gr nid sym =
  let gid = env.curr_gid in
  let binop_opt = match sym with
    | ADD -> Some C.Add | SUBTRACT -> Some C.Sub | TIMES -> Some C.Mul
    | FDIVIDE | IDIVIDE -> Some C.Div | EQUAL -> Some C.Eq
    | LESSER -> Some C.Lt | LESSER_EQUAL -> Some C.Le
    | GREATER -> Some C.Gt | GREATER_EQUAL -> Some C.Ge
    | OR -> Some C.LogOr | AND -> Some C.LogAnd
    | _ -> None
  in
  match binop_opt with
  | Some op ->
      let e1 = get_expr env gid nid 0 `In in
      let e2 = get_expr env gid nid 1 `In in
      let v_res = get_expr env gid nid 0 `Out in
      [C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (op, e1, e2)))]
  | None ->
      if sym = TYPECAST then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let ty = get_port_type env gr nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.Cast (ty, e)))]
      else if sym = RANGEGEN then
        let e1 = get_expr env gid nid 0 `In in
        let e2 = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Add, C.BinOp (C.Sub, e2, e1), C.LitInt 1)))]
      else if sym = NEGATE then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.UnaryOp (C.Negate, e)))]
      else if sym = DV_ELEMENT || sym = AELEMENT then
        let arr = get_expr env env.curr_gid nid 0 `In in
        let idx = get_expr env env.curr_gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        (* Get element type from the INPUT array type (dn=nid, dp=0), not the
           scalar output (get_elem_type looks at sn=nid which gives the scalar). *)
        let arr_ty_id = ES.fold (fun ((_, _), (dn, dp), t) acc ->
          if dn = nid && dp = 0 && t <> 0 then Some t else acc
        ) gr.eset None |> Option.value ~default:0 in
        let elem_ty = (try
          match TM.find arr_ty_id env.tm with
          | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm
          | _ -> Unknown_ty
        with _ -> Unknown_ty) in
        let cast_ty = match c_type_of_if1_ty env.tm elem_ty with C.Basic s -> s | _ -> "float" in
        let cast_ptr = C.Cast (C.Pointer (C.Basic cast_ty, []), C.Member (arr, "data")) in
        let idx_cast = C.Cast (C.Basic "size_t", C.BinOp (C.Sub, idx, C.Member (arr, "lower_bound"))) in
        [C.Expr (C.BinOp (C.Assign, v_res, C.Index (cast_ptr, idx_cast)))]
      else if sym = ASIZE || sym = DV_DIMENSION then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.Cast (C.Basic "int32_t", C.Member (arr, "size"))))]
      else if sym = ALIML then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.Cast (C.Basic "int32_t", C.Member (arr, "lower_bound"))))]
      else if sym = ALIMH then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.Cast (C.Basic "int32_t", 
            C.BinOp (C.Sub, C.BinOp (C.Add, C.Member (arr, "lower_bound"), 
                C.Cast (C.Basic "int64_t", C.Member (arr, "size"))), C.LitInt 1))))]
      else if sym = ASETL then
        let arr = get_expr env gid nid 0 `In in
        let lb = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, arr));
         C.Expr (C.BinOp (C.Assign, C.Member (v_res, "lower_bound"), C.Cast (C.Basic "int64_t", lb)))]
      else if sym = DV_CREATE then
        let lb = get_expr env gid nid 0 `In in
        let size = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let tid = match get_elem_type env gr nid with
          | Basic REAL -> 0 | Basic DOUBLE -> 1 | Basic INTEGRAL -> 2 | Basic BOOLEAN -> 3 | _ -> 0 in
        [C.Expr (C.BinOp (C.Assign, v_res,
           C.Call ("sisal_array_create", [lb; C.LitInt tid; C.Cast (C.Basic "int32_t", size)])))]
      else if sym = SELECT then
        let cond = get_expr env gid nid 0 `In in
        let v_then = get_expr env gid nid 1 `In in
        let v_else = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, C.Cond (cond, v_then, v_else)))]
      else if sym = FINALVALUE || sym = AGATHER then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, e))]
      else if sym = ERROR_NODE then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [C.Expr (C.BinOp (C.Assign, v_res, e))]
      else []

(* lower_if_graph: lower a graph that IS an IF compound.
   Called by lower_graph when it detects a SELECT node.
   Boundary inputs and pre-declared boundary-out vars are already in env.var_map
   (set up by lower_graph steps 2&3 before this call).
   SELECT absorption writes directly to those pre-declared boundary-out vars. *)
and lower_if_graph env gr gid =
  let wire_inputs child_cid child_gid =
    ES.fold (fun ((sn, sp), (dn, dp), _) m ->
      if dn = child_cid then
        FullPortMap.add (child_gid, 0, dp, `Out)
          (get_expr env gid sn sp `Out) m
      else m
    ) gr.eset env.var_map
  in
  let register_child_outputs child_cid child_gid child_env base_env =
    ES.fold (fun ((sn, sp), _, _) e ->
      if sn = child_cid then
        let expr = get_expr child_env child_gid 0 sp `In in
        { e with var_map = FullPortMap.add (gid, child_cid, sp, `Out) expr e.var_map }
      else e
    ) gr.eset { base_env with curr_gid = gid }
  in
  (* 1. Lower PREDICATE *)
  let pred_stmts, pred_gid, pred_cid, pred_env =
    match find_subgraph gr "PREDICATE" with
    | None -> failwith "lower_if_graph: no PREDICATE"
    | Some (pcid, pgr) ->
        let pgid = alloc_gid env.gid_table gid pcid in
        let vm = wire_inputs pcid pgid in
        let stmts, e' = lower_graph { env with var_map = vm } pgr pgid in
        stmts, pgid, pcid, e'
  in
  let pred_expr = get_expr pred_env pred_gid 0 0 `In in
  let env1 = register_child_outputs pred_cid pred_gid pred_env env in
  (* 2. Lower BODY (then-branch) *)
  let body_stmts, body_gid, body_cid, body_env_raw =
    match find_subgraph gr "BODY" with
    | None -> failwith "lower_if_graph: no BODY"
    | Some (bcid, bgr) ->
        let bgid = alloc_gid env.gid_table gid bcid in
        let vm = wire_inputs bcid bgid in
        let stmts, e' = lower_graph { env1 with var_map = vm } bgr bgid in
        stmts, bgid, bcid, e'
  in
  let body_env_m = ES.fold (fun ((sn, sp), _, _) m ->
    if sn = body_cid then
      let expr = get_expr body_env_raw body_gid 0 sp `In in
      FullPortMap.add (gid, body_cid, sp, `Out) expr m
    else m
  ) gr.eset body_env_raw.var_map in
  let body_env = { body_env_raw with var_map = body_env_m; curr_gid = gid } in
  (* 3. Lower ELSE branch; if it also has SELECT, lower_graph recurses into lower_if_graph *)
  let else_stmts, else_gid, else_cid, else_env_raw =
    match find_subgraph gr "ELSE" with
    | None -> failwith "lower_if_graph: no ELSE"
    | Some (ecid, egr) ->
        let egid = alloc_gid env.gid_table gid ecid in
        let vm = wire_inputs ecid egid in
        let stmts, e' = lower_graph { env1 with var_map = vm } egr egid in
        stmts, egid, ecid, e'
  in
  let else_env_m = ES.fold (fun ((sn, sp), _, _) m ->
    if sn = else_cid then
      let expr = get_expr else_env_raw else_gid 0 sp `In in
      FullPortMap.add (gid, else_cid, sp, `Out) expr m
    else m
  ) gr.eset else_env_raw.var_map in
  let else_env = { else_env_raw with var_map = else_env_m; curr_gid = gid } in
  (* 4. Absorb SELECT: assign branch results into the pre-declared boundary-out vars *)
  let sel_infos = find_boundary_selects gr in
  let then_assigns = List.filter_map (fun (sel_nid, bport) ->
    let res_v = C.Id (var_name gid 0 bport `In) in
    ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
      if dn = sel_nid && dp = 1 then
        Some (C.Expr (C.BinOp (C.Assign, res_v, get_expr body_env gid sn sp `Out)))
      else acc
    ) gr.eset None
  ) sel_infos in
  let else_assigns = List.filter_map (fun (sel_nid, bport) ->
    let res_v = C.Id (var_name gid 0 bport `In) in
    ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
      if dn = sel_nid && dp = 2 then
        Some (C.Expr (C.BinOp (C.Assign, res_v, get_expr else_env gid sn sp `Out)))
      else acc
    ) gr.eset None
  ) sel_infos in
  pred_stmts @ [C.If (pred_expr, body_stmts @ then_assigns, else_stmts @ else_assigns)]

and lower_for_initial env gr gid nid _cid loop_gr sub_gid var_map_child =
  let env_init = { env with var_map = var_map_child; parent_env = Some env } in

  let init_info = find_subgraph loop_gr "INIT" in
  let test_info = find_subgraph loop_gr "TEST" in
  let body_info = find_subgraph loop_gr "BODY" in
  let ret_info  = find_subgraph loop_gr "RETURNS" in

  match init_info, test_info, body_info, ret_info with
  | Some (init_nid, init_gr), Some (test_nid, test_gr), Some (body_nid, body_gr), Some (ret_nid, ret_gr) ->
      let init_gid = alloc_gid env.gid_table sub_gid init_nid in
      let test_gid = alloc_gid env.gid_table sub_gid test_nid in
      let body_gid = alloc_gid env.gid_table sub_gid body_nid in
      let ret_gid  = alloc_gid env.gid_table sub_gid ret_nid in

      (* 1. Lower INIT *)
      let init_stmts, e_init = lower_graph env_init init_gr init_gid in

      (* 2. Map INIT outputs to their names from symtab *)
      let init_out_names = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = 0 then
          match get_port_name init_gr sn sp `Out with
          | Some name -> IntMap.add dp name acc
          | None -> acc
        else acc
      ) init_gr.eset IntMap.empty in

      (* 3. Declare mutable state variables for each INIT output *)
      let state_vars =
        IntMap.bindings init_out_names |> List.map (fun (pid, name) ->
          let v = Printf.sprintf "v_g%d_state_%s" sub_gid name in
          let ty = get_port_type e_init init_gr 0 pid `In in
          (pid, name, v, ty)
        )
      in

      let init_decls = List.map (fun (pid, _name, v, ty) ->
        C.Decl (ty, v, Some (get_expr e_init init_gid 0 pid `In))
      ) state_vars in

      (* Helper: wire a subgraph by matching boundary input names to state variables *)
      let wire_subgraph child_gid child_gr =
        let vm = ref var_map_child in
        match NM.find_opt 0 child_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.iter (fun (_ty, pid, name) ->
              let sname = sanitize name in
              if sname <> "" then
                match List.find_opt (fun (_, n, _, _) -> n = sname) state_vars with
                | Some (_, _, v, _) ->
                    vm := FullPortMap.add (child_gid, 0, pid, `Out) (C.Id v) !vm
                | None -> ()
              else if pid < List.length state_vars then
                let (_, _, v, _) = List.nth state_vars pid in
                vm := FullPortMap.add (child_gid, 0, pid, `Out) (C.Id v) !vm
            ) ins;
            !vm
        | _ -> !vm
      in

      (* 4. Lower TEST - feeds from current state variables *)
      let test_vm = wire_subgraph test_gid test_gr in
      let test_stmts, e_test = lower_graph { env_init with var_map = test_vm } test_gr test_gid in
      let test_expr = get_expr e_test test_gid 0 0 `In in

      (* 5. Lower BODY - feeds from current state variables *)
      let body_vm = wire_subgraph body_gid body_gr in
      let body_stmts, e_body = lower_graph { env_init with var_map = body_vm } body_gr body_gid in

      (* 6. Update state from BODY outputs by matching names *)
      let body_out_names = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = 0 then
          match get_port_name body_gr sn sp `Out with
          | Some name -> IntMap.add dp name acc
          | None -> acc
        else acc
      ) body_gr.eset IntMap.empty in

      let update_stmts = ref [] in
      List.iter (fun (_pid, name, v, _ty) ->
        let found = ref false in
        IntMap.iter (fun dp n ->
          if n = name then begin
            update_stmts := C.Expr (C.BinOp (C.Assign, C.Id v, get_expr e_body body_gid 0 dp `In)) :: !update_stmts;
            found := true
          end
        ) body_out_names;
        if not !found then begin
          NM.iter (fun nid_ node ->
            if not !found then begin
              match node with
              | Simple (_, _, _, _, pr) | Compound (_, _, _, pr, _, _) ->
                  if List.exists (function Name s -> sanitize s = name | _ -> false) pr then begin
                    update_stmts := C.Expr (C.BinOp (C.Assign, C.Id v, get_expr e_body body_gid nid_ 0 `Out)) :: !update_stmts;
                    found := true
                  end
              | _ -> ()
            end
          ) body_gr.nmap
        end
      ) state_vars;

      (* 7. Lower RETURNS *)
      let ret_vm = wire_subgraph ret_gid ret_gr in
      let ret_stmts, e_ret = lower_graph { env_init with var_map = ret_vm } ret_gr ret_gid in

      (* 8. Map final results to compound node outputs *)
      let res_assigns =
        let outs = match NM.find_opt 0 ret_gr.nmap with Some (Boundary (_, o, _, _)) -> o | _ -> [] in
        List.mapi (fun i _ ->
          let res_v = get_expr env gid nid i `Out in
          C.Expr (C.BinOp (C.Assign, res_v, get_expr e_ret ret_gid 0 i `In))
        ) outs
      in

      init_stmts @ init_decls @
      [C.While (C.LitInt 1,
         test_stmts @
         [C.If (C.UnaryOp (C.LogNot, test_expr), [C.Break], [])] @
         body_stmts @
         !update_stmts)] @
      ret_stmts @ res_assigns

  | _ -> failwith "lower_for_initial: missing required subgraphs (INIT, TEST, BODY, RETURNS)"


and lower_forall env gr gid nid _cid loop_gr sub_gid var_map_child _pr =
  (* FORALL subgraphs (GENERATOR, BODY, RETURNS) share scope via GLOBAL-SYM:
     loop_gr.eset is empty.  Wire each child's boundary inputs by matching port
     names against the FORALL boundary.  Then lower GENERATOR and BODY
     explicitly rather than running lower_graph on the whole loop_gr. *)

  (* Build (lowercase_name, expr) association list from FORALL boundary *)
  let forall_named_inputs =
    match NM.find_opt 0 loop_gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.filter_map (fun (_ty_id, pid, name) ->
          let sname = String.lowercase_ascii name in
          if sname = "" then None
          else
            match FullPortMap.find_opt (sub_gid, 0, pid, `Out) var_map_child with
            | Some expr -> Some (sname, expr)
            | None -> None
        ) ins
    | _ -> []
  in

  (* Wire a child subgraph's boundary inputs by name-matching *)
  let wire_child_by_name child_gid child_gr =
    match NM.find_opt 0 child_gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.fold_left (fun vm (_ty_id, pid, name) ->
          let sname = String.lowercase_ascii name in
          match List.assoc_opt sname forall_named_inputs with
          | Some expr -> FullPortMap.add (child_gid, 0, pid, `Out) expr vm
          | None -> vm
        ) var_map_child ins
    | _ -> var_map_child
  in

  (* 1. Lower GENERATOR.
     count = boundary-out variable (pre-declared by lower_graph, in scope after gen_stmts).
     lo    = FORALL boundary port named "lo" (for "for i in lo, hi" RANGEGEN loops). *)
  let gen_stmts, gen_env, count_expr, lo_expr =
    match find_subgraph loop_gr "GENERATOR" with
    | None ->
        ([], { env with var_map = var_map_child; curr_gid = sub_gid },
         C.Id "0", C.LitInt 0)
    | Some (gen_nid, gen_gr) ->
        let gen_gid = alloc_gid env.gid_table sub_gid gen_nid in
        let gen_vm = wire_child_by_name gen_gid gen_gr in
        let stmts, e' =
          lower_graph { env with var_map = gen_vm; parent_env = Some env }
            gen_gr gen_gid in
        (* count: boundary-out of GENERATOR — the port dp where dn=0 in gen_gr *)
        let count_bp = ES.fold (fun (_, (dn, dp), _) acc ->
          if dn = 0 then Some dp else acc) gen_gr.eset None in
        let count = match count_bp with
          | Some dp -> C.Id (var_name gen_gid 0 dp `In)
          | None -> C.Id "0"
        in
        (* lo: start of the range.
           First try a named "lo" port on the FORALL boundary (e.g. "for i in lo, hi").
           If there is none (e.g. "for i in 1, N"), read RANGEGEN's port-0 input from
           the lowered generator env — for a Literal source use the value directly so
           we don't reference a variable that lives only in the inner gen scope. *)
        let has_rangegen = NM.exists (fun _ n ->
          match n with Simple (_, RANGEGEN, _, _, _) -> true | _ -> false) gen_gr.nmap in
        let lo = if has_rangegen then
          match List.assoc_opt "lo" forall_named_inputs with
          | Some expr -> expr
          | None ->
              NM.fold (fun rgn_nid node acc ->
                match node with
                | Simple (_, RANGEGEN, _, _, _) ->
                    let src = ES.fold (fun ((sn, sp), (dn, dp), _) a ->
                      if dn = rgn_nid && dp = 0 then Some (sn, sp) else a
                    ) gen_gr.eset None in
                    let res = (match src with
                     | None -> acc
                     | Some (sn, sp) ->
                         match NM.find_opt sn gen_gr.nmap with
                         | Some (Literal (_, _, value, _)) ->
                             (try C.LitInt (int_of_string value) with _ -> acc)
                         | _ -> get_expr e' gen_gid sn sp `Out) in
                    res
                | _ -> acc
              ) gen_gr.nmap (C.LitInt 0)
        else C.LitInt 0 in
        stmts, e', count, lo
  in

  (* 2. Allocate result array and set lower_bound *)
  let res_v = get_expr env gid nid 0 `Out in
  let elem_ty =
    match get_elem_type env gr nid with
    | Unknown_ty -> (try TM.find 8 env.tm with _ -> Unknown_ty)
    | ty -> ty
  in
  let tid = type_id_of_if1_ty env.tm elem_ty in
  let cast_ty =
    match c_type_of_if1_ty env.tm elem_ty with C.Basic s -> s | _ -> "float" in

  let alloc_stmt =
    C.Expr (C.BinOp (C.Assign, res_v,
      C.Call ("sisal_array_alloc_empty",
        [C.LitInt 1; C.LitInt tid; C.Cast (C.Basic "uint64_t", count_expr)]))) in
  let lo_bound_stmt =
    C.Expr (C.BinOp (C.Assign,
      C.Member (res_v, "lower_bound"),
      C.Cast (C.Basic "int64_t", lo_expr))) in

  (* 3. Lower BODY inside dispatch_apply *)
  match find_subgraph loop_gr "BODY" with
  | None ->
      gen_stmts @ [alloc_stmt; lo_bound_stmt]
  | Some (body_nid, body_gr) ->
      let body_gid = alloc_gid env.gid_table sub_gid body_nid in
      let index_var = Printf.sprintf "v_idx_g%d" body_gid in

      (* Wire BODY inputs by name; inject I = lo + (int32_t)idx if body uses I *)
      let body_vm = wire_child_by_name body_gid body_gr in
      let body_vm =
        match NM.find_opt 0 body_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.fold_left (fun vm (_ty_id, pid, name) ->
              if String.lowercase_ascii name = "i" then
                FullPortMap.add (body_gid, 0, pid, `Out)
                  (C.BinOp (C.Add, lo_expr,
                     C.Cast (C.Basic "int32_t", C.Id index_var))) vm
              else vm
            ) body_vm ins
        | _ -> body_vm
      in

      let body_stmts, _body_env =
        lower_graph
          { gen_env with var_map = body_vm; parent_env = Some gen_env }
          body_gr body_gid in

      (* Body result = BODY's pre-declared boundary-out variable at port 0 *)
      let body_res = C.Id (var_name body_gid 0 0 `In) in

      let cast_ptr =
        C.Cast (C.Pointer (C.Basic cast_ty, []), C.Member (res_v, "data")) in
      let write_stmt =
        C.Expr (C.BinOp (C.Assign,
          C.Index (cast_ptr, C.Id index_var), body_res)) in

      gen_stmts @
      [ alloc_stmt;
        lo_bound_stmt;
        C.GCDApply (count_expr,
          "dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0)",
          (index_var, body_stmts @ [write_stmt])) ]

and lower_if env gr gid nid _cid if_gr sub_gid var_map_child =
  (* Environment for the IF compound's internal graph *)
  let if_env = { env with
    var_map = var_map_child;
    curr_gid = sub_gid;
    parent_env = Some env } in
  (* Populate preds from if_gr edges *)
  let preds_if = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    FullPortMap.add (sub_gid, dn, dp, `In) (sub_gid, sn, sp, `Out) m
  ) if_gr.eset if_env.preds in
  let if_env = { if_env with preds = preds_if } in

  (* Wire all inputs of a compound child from if_gr edges *)
  let wire_inputs child_cid child_gid base_env =
    ES.fold (fun ((sn, sp), (dn, dp), _) m ->
      if dn = child_cid then
        FullPortMap.add (child_gid, 0, dp, `Out)
          (get_expr base_env sub_gid sn sp `Out) m
      else m
    ) if_gr.eset base_env.var_map
  in

  (* After lowering a child subgraph, register its output ports in if_env.
     Each edge (child_cid, sp) -> (...) in if_gr tells us the child has
     output port sp; the value is at (child_gid, 0, sp, In) post-lowering. *)
  let register_outputs child_cid child_gid child_env base_env =
    ES.fold (fun ((sn, sp), _, _) e ->
      if sn = child_cid then
        let expr = get_expr child_env child_gid 0 sp `In in
        { e with var_map =
            FullPortMap.add (sub_gid, child_cid, sp, `Out) expr e.var_map }
      else e
    ) if_gr.eset { base_env with curr_gid = sub_gid }
  in

  (* 1. Lower PREDICATE subgraph *)
  let pred_stmts, pred_gid, pred_cid, pred_env =
    match find_subgraph if_gr "PREDICATE" with
    | None -> failwith "lower_if: missing PREDICATE subgraph"
    | Some (pcid, pgr) ->
        let pgid = alloc_gid env.gid_table sub_gid pcid in
        let vm = wire_inputs pcid pgid if_env in
        let stmts, env' = lower_graph { if_env with var_map = vm } pgr pgid in
        stmts, pgid, pcid, env'
  in
  (* pred_expr = boolean output at boundary port 0 of PREDICATE *)
  let pred_expr = get_expr pred_env pred_gid 0 0 `In in
  (* Make PREDICATE outputs visible in if_env *)
  let if_env1 = register_outputs pred_cid pred_gid pred_env if_env in

  (* 2. Lower BODY (then-branch) subgraph *)
  let body_stmts, body_gid, body_cid, body_env_raw =
    match find_subgraph if_gr "BODY" with
    | None -> failwith "lower_if: missing BODY subgraph"
    | Some (bcid, bgr) ->
        let bgid = alloc_gid env.gid_table sub_gid bcid in
        let vm = wire_inputs bcid bgid if_env1 in
        let stmts, env' = lower_graph { if_env1 with var_map = vm } bgr bgid in
        stmts, bgid, bcid, env'
  in
  let body_env = ES.fold (fun ((sn, sp), _, _) m ->
    if sn = body_cid then
      let expr = get_expr body_env_raw body_gid 0 sp `In in
      FullPortMap.add (sub_gid, body_cid, sp, `Out) expr m
    else m
  ) if_gr.eset body_env_raw.var_map in
  let body_env = { body_env_raw with var_map = body_env; curr_gid = sub_gid } in

  (* 3. Lower ELSE branch subgraph.
     lower_graph will detect SELECT inside egr (elseif case) and call lower_if_graph
     recursively, so no special-casing needed here. *)
  let else_stmts, else_gid, else_cid, else_env_raw =
    match find_subgraph if_gr "ELSE" with
    | None -> failwith "lower_if: missing ELSE subgraph"
    | Some (ecid, egr) ->
        let egid = alloc_gid env.gid_table sub_gid ecid in
        let vm = wire_inputs ecid egid if_env1 in
        let stmts, env' = lower_graph { if_env1 with var_map = vm } egr egid in
        stmts, egid, ecid, env'
  in
  let else_env = ES.fold (fun ((sn, sp), _, _) m ->
    if sn = else_cid then
      let expr = get_expr else_env_raw else_gid 0 sp `In in
      FullPortMap.add (sub_gid, else_cid, sp, `Out) expr m
    else m
  ) if_gr.eset else_env_raw.var_map in
  let else_env = { else_env_raw with var_map = else_env; curr_gid = sub_gid } in

  (* 4. Absorb SELECT nodes: assign branch outputs into the parent pre-declared vars.
     find_boundary_selects returns [(sel_nid, bport)] where bport = output port of
     the IF compound in the parent graph.  get_expr env gid nid bport Out gives the
     pre-declared variable for that port (declared in parent lower_graph). *)
  let sel_infos = find_boundary_selects if_gr in

  let then_assigns = List.filter_map (fun (sel_nid, bport) ->
    let res_v = get_expr env gid nid bport `Out in
    ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
      if dn = sel_nid && dp = 1 then
        Some (C.Expr (C.BinOp (C.Assign, res_v,
          get_expr body_env sub_gid sn sp `Out)))
      else acc
    ) if_gr.eset None
  ) sel_infos in

  let else_assigns = List.filter_map (fun (sel_nid, bport) ->
    let res_v = get_expr env gid nid bport `Out in
    ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
      if dn = sel_nid && dp = 2 then
        Some (C.Expr (C.BinOp (C.Assign, res_v,
          get_expr else_env sub_gid sn sp `Out)))
      else acc
    ) if_gr.eset None
  ) sel_infos in

  pred_stmts
  @ [C.If (pred_expr,
           body_stmts @ then_assigns,
           else_stmts @ else_assigns)]

let lower_procedure tm nid node =
  next_dyn_gid := 1_000_000;
  match node with
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name s -> Some s | _ -> None) pr
        |> Option.value ~default:(Printf.sprintf "func_%d" nid) in
      let is_gpu_func = contains_substr (String.uppercase_ascii func_name) "GPU" in
      let gid_table = build_gid_table sub_gr in
      let sub_gid = 0 in  (* root graph of this function is always gid 0 *)
      (* Build port→ty_id from boundary output edges (source=node 0); the
         boundary metadata stores ty_id=0 for all entries so edges are authoritative. *)
      let boundary_port_types =
        ES.fold (fun ((sn, sp), _, ty_id) m ->
          if sn = 0 then IntMap.add sp ty_id m else m
        ) sub_gr.eset IntMap.empty in
      (* Fallback for LET_NON_REC-wrapped functions: no direct sn=0 edges in the
         outer graph.  Search compound children's inner graphs. *)
      let boundary_port_types =
        NM.fold (fun _ node m ->
          match node with
          | Compound (_, _, _, _, sg, _) ->
              ES.fold (fun ((sn, sp), _, t) acc ->
                if sn = 0 && t <> 0 && not (IntMap.mem sp acc)
                then IntMap.add sp t acc else acc
              ) sg.eset m
          | _ -> m
        ) sub_gr.nmap boundary_port_types
      in
      let params = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            let sorted_ins = List.sort (fun (_, p1, _) (_, p2, _) -> compare p1 p2) ins in
            List.filter_map (fun (ty_id, pid, name) ->
              let sname = sanitize name in
              if sname = "" then None
              else
                let final_ty_id = if ty_id <> 0 then ty_id else
                  try IntMap.find pid boundary_port_types with _ -> 0 in
                let if1_ty = try TM.find final_ty_id tm with _ -> Unknown_ty in
                (* Fallback: if name looks like an integer parameter, assume int32_t *)
                let c_ty = if if1_ty = Unknown_ty && (sname = "n" || sname = "i") then C.Basic "int32_t"
                           else c_type_of_if1_ty tm if1_ty in
                Some (c_ty, sname)
            ) sorted_ins
        | _ -> [] in
      let var_map = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.fold_left (fun m (_, pid, name) ->
              FullPortMap.add (sub_gid, 0, pid, `Out) (C.Id (sanitize name)) m
            ) FullPortMap.empty ins
        | _ -> FullPortMap.empty in
      let env = {
        tm; var_map;
        preds = FullPortMap.empty;
        curr_gid = sub_gid;
        parent_env = None;
        force_gpu = is_gpu_func;
        gid_table;
      } in
      let body_stmts, env_after = lower_graph env sub_gr sub_gid in

      let b_outs_from_metadata = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (_, outs, _, _)) -> List.mapi (fun i _ -> i) outs
        | _ -> [] in
      let b_outs_from_edges = ES.fold (fun (_, (dn, dp), _) acc ->
        if dn = 0 then IntSet.add dp acc else acc
      ) sub_gr.eset IntSet.empty |> IntSet.elements in
      let all_b_outs = List.sort_uniq compare (b_outs_from_metadata @ b_outs_from_edges) in

      let ret_exprs = List.map (fun pid ->
        (pid, C.Id (var_name sub_gid 0 pid `In))
      ) all_b_outs in

      let ret_count = List.length ret_exprs in
      if ret_count > 1 then
        let struct_name = func_name ^ "_results" in
        let fields = List.map (fun (dp, _) ->
          let ty = get_port_type env_after sub_gr 0 dp `In in
          ("res_" ^ string_of_int dp, ty)
        ) ret_exprs in
        let res_var = "res_obj" in
        let assigns = List.map (fun (dp, e) ->
          C.Expr (C.BinOp (C.Assign, C.Member (C.Id res_var, "res_" ^ string_of_int dp), e))
        ) ret_exprs in
        let final_body =
          body_stmts
          @ [C.Decl (C.Basic ("struct " ^ struct_name), res_var, None)]
          @ assigns
          @ [C.Return (Some (C.Id res_var))] in
        Some (
          { C.return_ty = C.Basic ("struct " ^ struct_name);
            name = func_name; params; body = final_body; extern_c = true },
          Some (struct_name, fields))
      else if ret_count = 1 then
        let (dp, e) = List.hd ret_exprs in
        let ty = get_port_type env_after sub_gr 0 dp `In in
        Some (
          { C.return_ty = ty; name = func_name;
            params; body = body_stmts @ [C.Return (Some e)]; extern_c = true },
          None)
      else
        Some (
          { C.return_ty = C.Void; name = func_name;
            params; body = body_stmts; extern_c = true },
          None)
  | _ -> None

let translate (gr : graph) : C.translation_unit =
  let _, tm, _ = gr.typemap in
  let results = NM.fold (fun id node acc ->
    match lower_procedure tm id node with
    | Some r -> r :: acc
    | None -> acc
  ) gr.nmap [] in
  let procedures = List.map fst results in
  let result_struct_decls =
    List.filter_map snd results
    |> List.map (fun (name, fields) -> C.Decl (C.Struct (name, fields), "", None)) in
  let seen_field_lists = ref [] in
  let record_structs = TM.fold (fun id ty acc ->
    match ty with
    | Record _ ->
        let fields = collect_record_fields tm id in
        if fields = [] || List.mem fields !seen_field_lists then acc
        else (
          seen_field_lists := fields :: !seen_field_lists;
          C.Decl (C.Struct ("struct_rec_" ^ string_of_int id, fields), "", None) :: acc
        )
    | _ -> acc
  ) tm [] in
  {
    filename = "out.cpp";
    includes = [
      "stdio.h"; "stdint.h"; "stdbool.h";
      "dispatch/dispatch.h"; "Accelerate/Accelerate.h"; "sisal_runtime.h";
    ];
    globals = record_structs @ result_struct_decls;
    procedures;
  }
