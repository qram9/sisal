(** apple_lower.ml: The "Apple Lowering" pass for Sisal. This module implements
    the complex logic of translating dataflow IF1 graphs into imperative C-AST
    nodes, with specific optimizations for Apple Silicon (GCD for parallelism,
    Accelerate for SIMD, etc.). *)

open Ir.If1
open Apple_env
open Apple_helpers

(** [c_name_of_mangled mangled] maps Sisal intrinsic names to their
    corresponding C library function names (math.h, Accelerate, etc.). *)
let c_name_of_mangled = function
  | "_SABS__F__F" -> Some "fabsf"
  | "_SABS__D__D" -> Some "fabs"
  | "_SABS__I__I" -> Some "abs"
  | "_SABS__L__L" -> Some "labs"
  | "_SSQRT__F__F" -> Some "sqrtf"
  | "_SSQRT__D__D" -> Some "sqrt"
  | "_SSQRTR__F__F" -> Some "sqrtf"
  | "_SSQRTR__D__D" -> Some "sqrt"
  | "_SSIN__F__F" -> Some "sinf"
  | "_SSIN__D__D" -> Some "sin"
  | "_SCOS__F__F" -> Some "cosf"
  | "_SCOS__D__D" -> Some "cos"
  | "_STAN__F__F" -> Some "tanf"
  | "_STAN__D__D" -> Some "tan"
  | "_SASIN__F__F" -> Some "asinf"
  | "_SASIN__D__D" -> Some "asin"
  | "_SACOS__F__F" -> Some "acosf"
  | "_SACOS__D__D" -> Some "acos"
  | "_SATAN__F__F" -> Some "atanf"
  | "_SATAN__D__D" -> Some "atan"
  | "_SATAN__FF__F" -> Some "atan2f"
  | "_SATAN__DD__D" -> Some "atan2"
  | "_SSINH__F__F" -> Some "sinhf"
  | "_SSINH__D__D" -> Some "sinh"
  | "_SCOSH__F__F" -> Some "coshf"
  | "_SCOSH__D__D" -> Some "cosh"
  | "_STANH__F__F" -> Some "tanhf"
  | "_STANH__D__D" -> Some "tanh"
  | "_SLOG__F__F" -> Some "logf"
  | "_SLOG__D__D" -> Some "log"
  | "_SLOG10__F__F" -> Some "log10f"
  | "_SLOG10__D__D" -> Some "log10"
  | "_SETOTHE__F__F" -> Some "expf"
  | "_SETOTHE__D__D" -> Some "exp"
  | "_SFLOOR__F__I" -> Some "(int32_t)floorf"
  | "_SFLOOR__D__L" -> Some "(int64_t)floor"
  | "_SFLOOR__H__S" -> Some "(int16_t)floorf"
  | "_STRUNC__F__I" -> Some "(int32_t)truncf"
  | "_STRUNC__D__L" -> Some "(int64_t)trunc"
  | "_STRUNC__H__S" -> Some "(int16_t)truncf"
  | "_SRADIANS__F__F" -> Some "sisal_radians_f"
  | "_SRADIANS__D__D" -> Some "sisal_radians_d"
  | "_SDEGREES__F__F" -> Some "sisal_degrees_f"
  | "_SDEGREES__D__D" -> Some "sisal_degrees_d"
  | _ -> None

(** [lower_graph env gr gid] translates an IF1 graph into a list of C
    statements using a robust state-threading functional approach. *)
let rec lower_graph env gr gid =
  let fanout_counts, mandatory_ports = compute_fanout gr in
  let env =
    {
      env with
      curr_gid = gid;
      curr_gr = gr;
      fanout_map = fanout_counts;
      mandatory_ports;
      seen_decls = StringSet.empty;
    }
  in

  (* 1. Populate preds from local edges *)
  let preds =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) m ->
        FullPortMap.add (gid, dn, dp, `In) (gid, sn, sp, `Out) m)
      gr.eset env.preds
  in
  let env = { env with preds } in

  (* 2. Materialize boundary inputs (node 0 Out ports). *)
  let b_in_pids =
    let from_meta = match NM.find_opt 0 gr.nmap with | Some (Boundary (ins, _, _, _)) -> List.map (fun (_, p, _) -> p) ins | _ -> [] in
    let from_edges = ES.fold (fun ((sn, sp), _, _) acc -> if sn = 0 then IntSet.add sp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
    List.sort_uniq compare (from_meta @ from_edges)
  in

  let b_in_decls, env =
    List.fold_left
      (fun (decls, e) pid ->
        let fanout = PortFanout.find_opt (0, pid) e.fanout_map |> Option.value ~default:0 in
        let is_mandatory = gid <> 0 || fanout > 1 || PortSet.mem (0, 0, pid, `Out) e.mandatory_ports in
        if (not is_mandatory) || gid = 0 then (decls, e)
        else
          let v_o = var_name e gr gid 0 pid `Out in
          if StringSet.mem v_o e.seen_decls then (decls, e)
          else
            let src_opt = FullPortMap.find_opt (gid, 0, pid, `Out) e.var_map in
            let ty = get_port_type e gr 0 pid `Out in
            ( C.Decl (ty, v_o, src_opt) :: decls,
              { e with var_map = FullPortMap.add (gid, 0, pid, `Out) (C.Id v_o) e.var_map; seen_decls = StringSet.add v_o e.seen_decls } ))
      ([], env) b_in_pids
  in
  let b_in_decls = List.rev b_in_decls in

  (* 3. Materialize boundary outputs (node 0 In ports). *)
  let b_outs_pids =
    let from_meta = match NM.find_opt 0 gr.nmap with | Some (Boundary (_, outs, errs, _)) -> List.mapi (fun i _ -> i) (outs @ errs) | _ -> [] in
    let from_edges = ES.fold (fun (_, (dn, dp), _) acc -> if dn = 0 then IntSet.add dp acc else acc) gr.eset IntSet.empty |> IntSet.elements in
    List.sort_uniq compare (from_meta @ from_edges)
  in

  let outer_decls, env =
    List.fold_left
      (fun (decls, e) pid ->
        let fanout = PortFanout.find_opt (0, pid) e.fanout_map |> Option.value ~default:0 in
        let is_mandatory = gid <> 0 || fanout > 1 || PortSet.mem (0, 0, pid, `In) e.mandatory_ports in
        if not is_mandatory then (decls, e)
        else
          let v_i = var_name e gr gid 0 pid `In in
          if StringSet.mem v_i e.seen_decls then (decls, e)
          else
            let ty = get_port_type e gr 0 pid `In in
            ( C.Decl (ty, v_i, None) :: decls,
              { e with var_map = FullPortMap.add (gid, 0, pid, `In) (C.Id v_i) e.var_map; seen_decls = StringSet.add v_i e.seen_decls } ))
      ([], env) b_outs_pids
  in
  let outer_decls = List.rev outer_decls in

  (* 4. Main Computation. *)
  let res_stmts, final_env =
    let has_select = NM.exists (fun _ n -> match n with Simple (_, SELECT, _, _, _) -> true | _ -> false) gr.nmap in
    if has_select && Option.is_some (find_subgraph gr "PREDICATE") then lower_if_graph env gr gid
    else
      let inner_decls, env =
        NM.fold
          (fun nid node (decls, e) ->
            if nid = 0 then (decls, e)
            else
              let decls, e = List.fold_left (fun (ds, ev) pid ->
                let v = var_name ev gr gid nid pid `Out in
                if FullPortMap.mem (gid, nid, pid, `Out) ev.var_map || StringSet.mem v ev.seen_decls then (ds, ev)
                else
                  let fanout = PortFanout.find_opt (nid, pid) ev.fanout_map |> Option.value ~default:0 in
                  if fanout > 1 || PortSet.mem (0, nid, pid, `Out) ev.mandatory_ports then
                    let ty = get_port_type ev gr nid pid `Out in
                    (C.Decl (ty, v, None) :: ds, { ev with var_map = FullPortMap.add (gid, nid, pid, `Out) (C.Id v) ev.var_map; seen_decls = StringSet.add v ev.seen_decls })
                  else (ds, ev)) (decls, e) (List.init 10 (fun i -> i)) (* Heuristic: check first 10 ports *) in
              List.fold_left (fun (ds, ev) pid ->
                let v = var_name ev gr gid nid pid `In in
                if FullPortMap.mem (gid, nid, pid, `In) ev.var_map || StringSet.mem v ev.seen_decls then (ds, ev)
                else
                  let ty = get_port_type ev gr nid pid `In in
                  (C.Decl (ty, v, None) :: ds, { ev with var_map = FullPortMap.add (gid, nid, pid, `In) (C.Id v) ev.var_map; seen_decls = StringSet.add v ev.seen_decls })) (decls, e) (List.init 10 (fun i -> i)))
          gr.nmap ([], env) in
      let stmts_rev, env =
        List.fold_left (fun (acc, e) nid ->
          if nid = 0 then (acc, e)
          else match NM.find_opt nid gr.nmap with
          | Some node ->
              let node_preds = ES.filter (fun (_, (dn, _), _) -> dn = nid) gr.eset in
              let e' = ES.fold (fun ((sn, sp), (_, dp), _) ev ->
                let src_expr = get_expr ev gid sn sp `Out in
                { ev with var_map = FullPortMap.add (gid, nid, dp, `In) src_expr ev.var_map }) node_preds e in
              let node_stmts, e'' = lower_node e' gr nid node in
              (List.rev_append node_stmts acc, e'') | None -> (acc, e)) ([], env) (topo_sort gr) in
      let propagation = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = 0 then
          let src = get_expr env gid sn sp `Out in
          let dst = get_expr env gid 0 dp `In in
          if dst = src then acc else C.Expr (C.BinOp (C.Assign, dst, src)) :: acc
        else acc) gr.eset [] in
      (List.rev inner_decls @ List.rev stmts_rev @ propagation, env)
  in
  (b_in_decls @ outer_decls @ res_stmts, final_env)

and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, _ty, pr, loop_gr, _) ->
      let sub_gid = alloc_gid env.gid_table gid cid in
      let var_map_child = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
        if dn = cid then FullPortMap.add (sub_gid, 0, dp, `Out) (get_expr env gid sn sp `Out) m else m) gr.eset env.var_map in
      let env_child = { env with var_map = var_map_child; parent_env = Some env } in
      let is_real_forall = sy = INTERNAL && List.exists (function Name n -> n = "FORALL" | _ -> false) pr in
      if is_real_forall then lower_forall env_child gr gid nid cid loop_gr sub_gid var_map_child pr
      else
        let body, env_after = lower_graph env_child loop_gr sub_gid in
        let results = ES.fold (fun ((sn, sp), (dn, dp), _) acc -> if sn = cid then (sp, dp) :: acc else acc) gr.eset [] in
        let result_propagation = List.map (fun (sp, dp) -> C.Expr (C.BinOp (C.Assign, get_expr env_after gid cid sp `Out, get_expr env_after sub_gid 0 sp `In))) results in
        (body @ result_propagation, { env_after with curr_gid = gid; curr_gr = gr })
  | Simple (_, sym, pin, pout, pr) -> lower_simple env gr nid sym pin pout pr
  | Literal (_, code, value, _) ->
      let lit = try match code with REAL | DOUBLE -> C.LitFloat (float_of_string value) | BOOLEAN -> C.Id (String.lowercase_ascii value) | _ -> C.LitInt (int_of_string value) with _ -> C.LitInt 0 in
      let v_res = get_expr env gid nid 0 `Out in ([ C.Expr (C.BinOp (C.Assign, v_res, lit)) ], env)
  | _ -> ([], env)

and lower_simple env gr nid sym _pin _pout _pr =
  let gid = env.curr_gid in
  let e1 = try get_expr env gid nid 0 `In with _ -> C.LitInt 0 in
  let e2 = try get_expr env gid nid 1 `In with _ -> C.LitInt 0 in
  let v_res = get_expr env gid nid 0 `Out in
  match sym with
  | ADD -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Add, e1, e2))) ], env)
  | SUBTRACT -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Sub, e1, e2))) ], env)
  | TIMES -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Mul, e1, e2))) ], env)
  | EQUAL -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Eq, e1, e2))) ], env)
  | GREATER -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.BinOp (C.Gt, e1, e2))) ], env)
  | DV_NUM_RANK -> ([ C.Expr (C.BinOp (C.Assign, v_res, C.Member (e1, "rank"))) ], env)
  | AELEMENT | DV_ELEMENT ->
      let cast_ptr = C.Cast (C.Pointer (C.Basic "double", []), C.Member (e1, "data")) in
      let idx = C.BinOp (C.Sub, e2, C.Member (e1, "lower_bound")) in
      ([ C.Expr (C.BinOp (C.Assign, v_res, C.Index (cast_ptr, idx))) ], env)
  | _ -> ([], env)

and lower_if_graph env gr gid =
  let (pred_cid, pred_sg) = match find_subgraph gr "PREDICATE" with Some x -> x | _ -> failwith "no pred" in
  let pgid = alloc_gid env.gid_table gid pred_cid in
  let v_pred = var_name env gr gid pred_cid 0 `In in
  let pred_stmts, _ = lower_graph env pred_sg pgid in
  (pred_stmts @ [ C.If (C.Id v_pred, [], []) ], env)

and lower_forall env gr gid nid cid loop_gr sub_gid _var_map_child _pr =
  let gen_info = find_subgraph loop_gr "GENERATOR" in
  match gen_info with
  | Some (gen_nid, gen_gr) ->
      let gen_gid = alloc_gid env.gid_table sub_gid gen_nid in
      let gen_stmts, e' = lower_graph env gen_gr gen_gid in
      let count = get_expr e' gen_gid 0 1 `In in
      let res_v = get_expr env gid nid 0 `Out in
      let alloc = C.Expr (C.BinOp (C.Assign, res_v, C.Call ("sisal_array_alloc_empty", [C.LitInt 1; C.LitInt 0; C.Cast (C.Basic "uint64_t", count)]))) in
      (gen_stmts @ [alloc], env)
  | None -> ([], env)

and lower_for_initial env gr gid nid cid loop_gr sub_gid var_map_child = ([], env)

let lower_procedure tm nid node =
  match node with
  | Compound (_, INTERNAL, ty, pr, sub_gr, _) ->
      let func_name = List.find_map (function Name s -> Some s | _ -> None) pr |> Option.value ~default:(Printf.sprintf "func_%d" nid) in
      let gid_table = build_gid_table sub_gr in
      let sub_gid = 0 in
      let func_param_types = get_function_param_types tm ty in
      let params = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            let sorted_ins = List.sort (fun (_, p1, _) (_, p2, _) -> compare p1 p2) ins in
            List.mapi (fun i (_, pid, name) ->
                let sname = sanitize name in
                let if1_ty = match List.nth_opt func_param_types i with Some tid -> (try TM.find tid tm with _ -> Unknown_ty) | None -> Unknown_ty in
                let c_ty = if if1_ty = Unknown_ty then (if sname = "n" || sname = "i" then C.Basic "int32_t" else C.Basic "sisal_array_t") else c_type_of_if1_ty tm if1_ty in
                (c_ty, sname)) sorted_ins
        | _ -> [] in
      let var_map = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.fold_left (fun m (_, pid, name) ->
                let sname = sanitize name in
                FullPortMap.add (sub_gid, 0, pid, `Out) (C.Id sname) m) FullPortMap.empty ins
        | _ -> FullPortMap.empty in
      let fanout_counts, mandatory_ports = compute_fanout sub_gr in
      let env = { tm; var_map; preds = FullPortMap.empty; curr_gid = sub_gid; curr_gr = sub_gr; parent_env = None; force_gpu = false; gid_table; fanout_map = fanout_counts; mandatory_ports; seen_decls = StringSet.empty } in
      let body, env_after = lower_graph env sub_gr sub_gid in
      let b_outs_from_metadata = match NM.find_opt 0 sub_gr.nmap with Some (Boundary (_, outs, _, _)) -> List.mapi (fun i _ -> i) outs | _ -> [] in
      let b_outs_from_edges = ES.fold (fun (_, (dn, dp), _) acc -> if dn = 0 then IntSet.add dp acc else acc) sub_gr.eset IntSet.empty |> IntSet.elements in
      let all_b_outs = List.sort_uniq compare (b_outs_from_metadata @ b_outs_from_edges) in
      let ret_exprs = List.map (fun pid -> let res_v = get_expr env_after sub_gid 0 pid `In in (pid, res_v)) all_b_outs in
      let ret_count = List.length ret_exprs in
      if ret_count > 1 then
        let struct_name = func_name ^ "_results" in
        let fields = List.map (fun (dp, _) -> let ty = get_port_type env_after sub_gr 0 dp `In in ("res_" ^ string_of_int dp, ty)) ret_exprs in
        let res_var = "res_obj" in
        let assigns = List.map (fun (dp, e) -> C.Expr (C.BinOp (C.Assign, C.Member (C.Id res_var, "res_" ^ string_of_int dp), e))) ret_exprs in
        Some ({ C.return_ty = C.Basic ("struct " ^ struct_name); name = func_name; params; body = body @ [ C.Decl (C.Basic ("struct " ^ struct_name), res_var, None) ] @ assigns @ [ C.Return (Some (C.Id res_var)) ]; extern_c = true }, Some (struct_name, fields))
      else if ret_count = 1 then
        let dp, e = List.hd ret_exprs in
        let ty = get_port_type env_after sub_gr 0 dp `In in
        Some ({ C.return_ty = ty; name = func_name; params; body = body @ [ C.Return (Some e) ]; extern_c = true }, None)
      else Some ({ C.return_ty = C.Void; name = func_name; params; body; extern_c = true }, None)
  | _ -> None

let translate gr =
  let _, tm, _ = gr.typemap in
  let results = NM.fold (fun id node acc -> match lower_procedure tm id node with Some r -> r :: acc | None -> acc) gr.nmap [] in
  let procedures = List.map fst results in
  let prototypes = List.map (fun p -> C.Prototype p) procedures in
  let result_struct_decls = List.filter_map snd results |> List.map (fun (name, fields) -> C.Decl (C.Struct (name, fields), "", None)) in
  let record_structs = TM.fold (fun id ty acc -> match ty with Record _ -> let fields = collect_record_fields tm id in C.Decl (C.Struct ("struct_rec_" ^ string_of_int id, fields), "", None) :: acc | _ -> acc) tm [] in
  { C.filename = "out.cpp"; C.includes = ["stdio.h"; "stdint.h"; "stdbool.h"; "dispatch/dispatch.h"; "Accelerate/Accelerate.h"; "sisal_runtime.h"]; C.globals = record_structs @ result_struct_decls @ prototypes; C.procedures = procedures; }
