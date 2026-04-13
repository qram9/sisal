open Ir.If1
module C = Ir.C_ast

module FullPortMap = Map.Make(struct
  type t = int * int * int (* gr_id, node_id, port_id *)
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
  preds : (int * int * int) FullPortMap.t;
  curr_gr : int;
  parent_node : (int * int) option; (* gid, nid *)
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
  let s = if String.starts_with ~prefix:"OLD " name then String.sub name 4 (String.length name - 4)
          else if String.starts_with ~prefix:"OLD_" name then String.sub name 4 (String.length name - 4)
          else name in
  let s = String.map (fun c -> if c = ' ' then '_' else c) s in
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
  | _ -> C.Basic "float"

let c_type_of_if1_ty _tm = function
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
  | Array_dv _ | Array_ty _ -> 10 
  | _ -> 0

let rec get_expr ?(depth=0) env gid nid pid =
  if depth > 50 then C.Id "REC_LIMIT" else
  match FullPortMap.find_opt (gid, nid, pid) env.var_map with
  | Some e -> e
  | None -> 
      match FullPortMap.find_opt (gid, nid, pid) env.preds with
      | Some (sg, sn, sp) -> get_expr ~depth:(depth+1) env sg sn sp
      | None -> 
          if nid = 0 then
            match env.parent_node with
            | Some (pgid, pnid) -> get_expr ~depth:(depth+1) env pgid pnid pid
            | None -> C.Id (Printf.sprintf "v_g%d_n%d_p%d" gid nid pid)
          else
            C.Id (Printf.sprintf "v_g%d_n%d_p%d" gid nid pid)

let get_port_type env gr nid pid =
  let ty_id = ES.fold (fun ((sn, sp), (dn, dp), t) acc ->
    if (sn = nid && sp = pid) || (dn = nid && dp = pid) then Some t else acc
  ) gr.eset None |> Option.value ~default:0 in
  try 
    let if1_ty = TM.find ty_id env.tm in
    c_type_of_if1_ty env.tm if1_ty
  with _ -> C.Basic "float"

let get_elem_type env gr nid =
  let ty_id = ES.fold (fun ((sn, sp), _, t) acc ->
    if sn = nid && sp = 0 then Some t else acc
  ) gr.eset None |> Option.value ~default:0 in
  try 
    match TM.find ty_id env.tm with
    | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm
    | _ -> Unknown_ty
  with _ -> Unknown_ty

let string_of_pragma = function
  | Name s | Ast_type s | Subscript s -> s
  | _ -> ""

let get_boundary_output_expr env gid gr port =
  ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
    if dn = 0 && dp = port then Some (get_expr env gid sn sp) else acc
  ) gr.eset None

let rec collect_record_fields tm label =
  match TM.find_opt label tm with
  | Some (Record (field_ty_id, next_label, name)) ->
      let s_name = String.trim name in
      if s_name = "" || s_name = "UNKNOWN" then collect_record_fields tm next_label
      else
        let field_ty_val = try TM.find field_ty_id tm with _ -> Unknown_ty in
        if field_ty_val = Unknown_ty then collect_record_fields tm next_label
        else
          let field_ty = c_type_of_if1_ty tm field_ty_val in
          (sanitize name, field_ty) :: collect_record_fields tm next_label
  | _ -> []

let has_hint hint pr =
  let hint_u = String.uppercase_ascii hint in
  let match_p p = contains_substr (String.uppercase_ascii (string_of_pragma p)) hint_u in
  List.exists match_p pr

let topo_sort gr =
  let rec visit (visited, stack) nid =
    if IntSet.mem nid visited then (visited, stack)
    else
      let predecessors = ES.fold (fun ((sn, _), (dn, _), _) acc ->
        if dn = nid then sn :: acc else acc
      ) gr.eset [] in
      let visited, stack = List.fold_left visit (IntSet.add nid visited, stack) predecessors in
      (visited, nid :: stack)
  in
  let nodes = NM.bindings gr.nmap |> List.map fst in
  let _, stack = List.fold_left visit (IntSet.empty, []) nodes in
  List.rev stack

let find_subgraph gr name =
  NM.choose_opt (NM.filter (fun _ n ->
    match n with
    | Compound (_, _, _, pr, _, _) ->
        let s_name = List.fold_left (fun acc p -> acc ^ (string_of_pragma p)) "" pr in
        contains_substr (String.uppercase_ascii s_name) (String.uppercase_ascii name)
    | _ -> false
  ) gr.nmap) |> Option.map (fun (id, n) -> match n with Compound (_,_,_,_,g,_) -> (id, g) | _ -> assert false)

let rec lower_graph env gr gid =
  let env = { env with curr_gr = gid } in
  let preds = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    FullPortMap.add (gid, dn, dp) (gid, sn, sp) m
  ) gr.eset env.preds in
  (* Map boundary ports to parent graph ports if applicable *)
  let preds = match NM.find_opt 0 gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.fold_left (fun m (_, pid, _) ->
          match env.parent_node with
          | Some (pgid, pnid) -> FullPortMap.add (gid, 0, pid) (pgid, pnid, pid) m
          | None -> m
        ) preds ins
    | _ -> preds in
  let var_map = match NM.find_opt 0 gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.fold_left (fun m (_, pid, name) ->
          let s_name = sanitize name in
          if s_name = "" || FullPortMap.mem (gid, 0, pid) m then m
          else FullPortMap.add (gid, 0, pid) (C.Id s_name) m
        ) env.var_map ins
    | _ -> env.var_map in
  let env = { env with preds; var_map } in
  let sorted_nids = topo_sort gr in
  let stmts, env_after = List.fold_left (fun (acc_stmts, curr_env) nid ->
    if nid = 0 then acc_stmts, curr_env 
    else match NM.find_opt nid gr.nmap with
    | Some node ->
        let new_stmts, next_env = lower_node curr_env gr nid node in
        acc_stmts @ new_stmts, next_env
    | None -> acc_stmts, curr_env
  ) ([], env) sorted_nids in
  let var_map_final = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
    if dn = 0 then FullPortMap.add (gid, 0, dp) (get_expr env_after gid sn sp) m else m
  ) gr.eset env_after.var_map in
  stmts, { env_after with var_map = var_map_final }

and lower_node env gr nid node =
  let gid = env.curr_gr in
  match node with
  | Compound (cid, sy, ty, pr, loop_gr, assoc) ->
      let sub_gid = gen_gr_id () in
      
      let map_inputs boundary_gid curr_env =
          ES.fold (fun ((sn, sp), (dn, dp), _) e ->
              if dn = cid then 
                let expr = get_expr e gid sn sp in
                { e with var_map = FullPortMap.add (boundary_gid, 0, dp) expr e.var_map }
              else e
            ) gr.eset curr_env
      in
      
      let is_real_forall = (sy = INTERNAL && List.exists (function Name n -> n = "FORALL" | _ -> false) pr) in
      let is_gpu = env.force_gpu || has_hint "GPU" pr in
      
      if is_real_forall then
          let body_info = find_subgraph loop_gr "BODY" in
          let env_loop_init = map_inputs sub_gid env in
          let env_loop = { env_loop_init with curr_gr = sub_gid; parent_node = Some (gid, cid) } in
          let _, env_after_loop_bound = lower_graph env_loop loop_gr sub_gid in
          
          let count_v = match NM.choose_opt (NM.filter (fun _ n -> match n with Simple(_, ASIZE, _, _, _) -> true | _ -> false) gr.nmap) with
            | Some (size_nid, _) -> get_expr env gid size_nid 2
            | None -> get_expr env gid cid 1
          in
          
          let res_v_name = Printf.sprintf "v_arr_g%d_n%d" gid nid in
          let elem_ty = get_elem_type env gr nid in
          let tid = type_id_of_if1_ty env.tm elem_ty in
          
          if is_gpu then
              let args = [get_expr env gid cid 0; get_expr env gid cid 3; C.Id res_v_name] in
              let gpu_call = C.Expr (C.Call ("sisal_gpu_vector_add", args)) in
              let cpu_init = C.Decl (C.Basic "sisal_array_t", res_v_name, Some (C.Call ("sisal_array_alloc_empty", [C.LitInt 1; C.LitInt tid; C.Cast (C.Basic "uint64_t", count_v)]))) in
              let var_map = FullPortMap.add (gid, nid, 0) (C.Id res_v_name) env.var_map in
              [cpu_init; gpu_call], { env with var_map }
          else
              let cpu_init = C.Decl (C.Basic "sisal_array_t", res_v_name, Some (C.Call ("sisal_array_alloc_empty", [C.LitInt 1; C.LitInt tid; C.Cast (C.Basic "uint64_t", count_v)]))) in
              match body_info with
              | Some (body_id, body_gr) ->
                  let body_gid = gen_gr_id () in
                  let env_body_pre = { env_after_loop_bound with curr_gr = body_gid; parent_node = Some (sub_gid, body_id) } in
                  let index_port = 2 in
                  (* ADJUSTMENT: Map loop index 'i' to 'i + 1' for Sisal logic *)
                  let var_map = FullPortMap.add (body_gid, 0, index_port) (C.BinOp (C.Add, C.Id "i", C.LitInt 1)) env_body_pre.var_map in
                  let body_env = { env_body_pre with var_map } in
                  let body_stmts, env_after_body = lower_graph body_env body_gr body_gid in
                  let body_res = get_boundary_output_expr env_after_body body_gid body_gr 0 |> Option.value ~default:(C.Id "0.0f") in
                  let cast_ptr = C.Cast (C.Pointer(C.Basic "float", []), C.Member (C.Id res_v_name, "data")) in
                  let update_stmt = C.Expr (C.BinOp (C.Assign, C.Index (cast_ptr, C.Id "i"), body_res)) in
                  let gcd_stmt = C.GCDApply (count_v, "dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0)", ("i", body_stmts @ [update_stmt])) in
                  let var_map = FullPortMap.add (gid, nid, 0) (C.Id res_v_name) env_after_body.var_map in
                  [cpu_init; gcd_stmt], { env_after_body with var_map; curr_gr = gid }
              | None -> [cpu_init], env
      else
          let env_sub_init = map_inputs sub_gid env in
          let env_sub = { env_sub_init with curr_gr = sub_gid; parent_node = Some (gid, cid) } in
          let stmts, env_after_sub = lower_graph env_sub loop_gr sub_gid in
          let var_map = ES.fold (fun ((sn, sp), (dn, dp), _) m ->
              if dn = 0 then FullPortMap.add (gid, cid, dp) (get_expr env_after_sub sub_gid sn sp) m else m
            ) loop_gr.eset env_after_sub.var_map in
          stmts, { env_after_sub with var_map; curr_gr = gid }
  | Simple (_, sym, _, pout, _) ->
      begin match match sym with
        | ADD -> Some C.Add | SUBTRACT -> Some C.Sub | TIMES -> Some C.Mul 
        | FDIVIDE | IDIVIDE -> Some C.Div | EQUAL -> Some C.Eq 
        | LESSER -> Some C.Lt | LESSER_EQUAL -> Some C.Le 
        | GREATER -> Some C.Gt | GREATER_EQUAL -> Some C.Ge | _ -> None
      with
      | Some op ->
          let e1 = get_expr env gid nid 0 in 
          let e2 = get_expr env gid nid 1 in
          let ty = get_port_type env gr nid 0 in
          let v_name = Printf.sprintf "v_g%d_n%d" gid nid in
          let stmt = C.Decl (ty, v_name, Some (C.BinOp (op, e1, e2))) in
          let var_map = Array.fold_left (fun m ps ->
              let pid = try int_of_string (String.trim ps) with _ -> 0 in
              FullPortMap.add (gid, nid, pid) (C.Id v_name) m
            ) env.var_map pout in
          let var_map = FullPortMap.add (gid, nid, 0) (C.Id v_name) var_map in
          [stmt], { env with var_map }
      | None -> 
          if sym = TYPECAST then
            let e = get_expr env gid nid 0 in
            let ty = get_port_type env gr nid 0 in
            let v_name = Printf.sprintf "v_cast_g%d_n%d" gid nid in
            let stmt = C.Decl (ty, v_name, Some (C.Cast (ty, e))) in
            let var_map = Array.fold_left (fun m ps ->
                let pid = try int_of_string (String.trim ps) with _ -> 0 in
                FullPortMap.add (gid, nid, pid) (C.Id v_name) m
              ) env.var_map pout in
            let var_map = FullPortMap.add (gid, nid, 0) (C.Id v_name) var_map in
            [stmt], { env with var_map }
          else if sym = RANGEGEN then
            let count = get_expr env gid nid 1 in 
            let var_map = Array.fold_left (fun m ps ->
                let pid = try int_of_string (String.trim ps) with _ -> 0 in
                FullPortMap.add (gid, nid, pid) count m
              ) env.var_map pout in
            let var_map = FullPortMap.add (gid, nid, 0) count var_map in
            [], { env with var_map }
          else if sym = DV_ELEMENT || sym = AELEMENT then
            let arr = get_expr env gid nid 0 in
            let idx = get_expr env gid nid 1 in
            let ty = get_port_type env gr nid 0 in
            let v_name = Printf.sprintf "v_elem_g%d_n%d" gid nid in
            let cast_ptr = C.Cast (C.Pointer(C.Basic "float", []), C.Member (arr, "data")) in
            let stmt = C.Decl (ty, v_name, Some (C.Index (cast_ptr, C.BinOp(C.Sub, idx, C.Member(arr, "lower_bound"))))) in
            let var_map = Array.fold_left (fun m ps ->
                let pid = try int_of_string (String.trim ps) with _ -> 0 in
                FullPortMap.add (gid, nid, pid) (C.Id v_name) m
              ) env.var_map pout in
            let var_map = FullPortMap.add (gid, nid, 0) (C.Id v_name) var_map in
            [stmt], { env with var_map }
          else if sym = ASIZE || sym = DV_DIMENSION then
            let arr = get_expr env gid nid 0 in
            let v_name = Printf.sprintf "v_size_g%d_n%d" gid nid in
            let stmt = C.Decl (C.Basic "int32_t", v_name, Some (C.Cast (C.Basic "int32_t", C.Member (arr, "size")))) in
            let var_map = Array.fold_left (fun m ps ->
                let pid = try int_of_string (String.trim ps) with _ -> 0 in
                FullPortMap.add (gid, nid, pid) (C.Id v_name) m
              ) env.var_map pout in
            let var_map = FullPortMap.add (gid, nid, 0) (C.Id v_name) var_map in
            [stmt], { env with var_map }
          else if sym = INVOCATION then
            let func_name = List.find_map (function Name s -> Some s | _ -> None) pr |> Option.value ~default:"unknown" in
            let arg_count = ES.fold (fun (_, (dn, dp), _) acc -> if dn = nid then max acc (dp + 1) else acc) gr.eset 0 in
            let args = List.init arg_count (fun i -> get_expr env gid nid i) in
            let ty = get_port_type env gr nid 0 in
            let v_name = Printf.sprintf "v_call_g%d_n%d" gid nid in
            let call_name = if env.force_gpu then "sisal_gpu_" ^ func_name else func_name in
            let stmt = C.Decl (ty, v_name, Some (C.Call (call_name, args))) in
            let var_map = Array.fold_left (fun m ps ->
                let pid = try int_of_string (String.trim ps) with _ -> 0 in
                FullPortMap.add (gid, nid, pid) (C.Id v_name) m
              ) env.var_map pout in
            let var_map = FullPortMap.add (gid, nid, 0) (C.Id v_name) var_map in
            [stmt], { env with var_map }
          else [], env
      end
  | Literal (_, code, value, pout) ->
      let v_name = Printf.sprintf "lit_g%d_n%d" gid nid in
      let lit = try 
        match code with 
        | REAL | DOUBLE -> C.LitFloat (float_of_string value)
        | _ -> C.LitInt (int_of_string value)
      with _ -> C.LitInt 0 in
      let stmt = C.Decl (c_type_of_if1_basic code, v_name, Some lit) in
      let var_map = Array.fold_left (fun m ps ->
          let pid = try int_of_string (String.trim ps) with _ -> 0 in
          FullPortMap.add (gid, nid, pid) (C.Id v_name) m
        ) env.var_map pout in
      let var_map = FullPortMap.add (gid, nid, 0) (C.Id v_name) var_map in
      [stmt], { env with var_map }
  | Boundary (ins, _, _, _) ->
      let var_map = List.fold_left (fun m (_, pid, name) ->
        let s_name = sanitize name in
        if s_name = "" || FullPortMap.mem (gid, 0, pid) m then m
        else FullPortMap.add (gid, 0, pid) (C.Id s_name) m
      ) env.var_map ins in
      [], { env with var_map }
  | _ -> [], env

let lower_procedure tm nid node =
  match node with
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      let func_name = List.find_map (function Name s -> Some s | _ -> None) pr 
                      |> Option.value ~default:(Printf.sprintf "func_%d" nid) in
      let is_gpu_func = contains_substr (String.uppercase_ascii func_name) "GPU" in
      let sub_gid = gen_gr_id () in
      let params = match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            let sorted_ins = List.sort (fun (_, p1, _) (_, p2, _) -> compare p1 p2) ins in
            List.map (fun (_, pid, name) ->
              let ty_id = ES.fold (fun ((sn, sp), _, t) acc ->
                if sn = 0 && sp = pid then Some t else acc
              ) sub_gr.eset None |> Option.value ~default:0 in
              let if1_ty = try TM.find ty_id tm with _ -> Unknown_ty in
              let c_ty = match if1_ty with
                | Array_dv _ | Array_ty _ -> C.Basic "sisal_array_t"
                | Record (id, _, _) -> C.Basic ("struct struct_rec_" ^ string_of_int id)
                | Basic b -> c_type_of_if1_basic b
                | _ -> C.Basic "sisal_array_t"
              in
              (c_ty, sanitize name)
            ) sorted_ins
        | _ -> [] in
      let env = { tm; var_map = FullPortMap.empty; preds = FullPortMap.empty; curr_gr = sub_gid; parent_node = None; force_gpu = is_gpu_func } in
      let body, env_after = lower_graph env sub_gr sub_gid in
      let ret_exprs = ES.fold (fun ((sn, sp), (dn, dp), _) acc ->
        if dn = 0 then (dp, get_expr env_after sub_gid sn sp) :: acc else acc
      ) sub_gr.eset [] |> List.sort (fun (p1, _) (p2, _) -> compare p1 p2) in
      let ret_count = List.length ret_exprs in
      if ret_count > 1 then
          let struct_name = func_name ^ "_results" in
          let fields = List.mapi (fun i (dp, _) ->
              let ty_id = ES.fold (fun (_, (dn, dp2), t) acc ->
                if (dn = 0 && dp = dp2) then Some t else acc
              ) sub_gr.eset None |> Option.value ~default:0 in
              let ty = try TM.find ty_id tm |> c_type_of_if1_ty tm with _ -> C.Basic "float" in
              ("res_" ^ string_of_int i, ty)
            ) ret_exprs in
          let res_var = "res_obj" in
          let assigns = List.mapi (fun i (_, e) ->
              C.Expr (C.BinOp (C.Assign, C.Member (C.Id res_var, "res_" ^ string_of_int i), e))
            ) ret_exprs in
          let final_body = body @ [C.Decl (C.Basic ("struct " ^ struct_name), res_var, None)] @ assigns @ [C.Return (Some (C.Id res_var))] in
          Some ({ C.return_ty = C.Basic ("struct " ^ struct_name); name = func_name; params; body = final_body; extern_c = true }, Some (struct_name, fields))
      else if ret_count = 1 then
          let (_, e) = List.hd ret_exprs in
          let ty_id = ES.fold (fun (_, (dn, dp), t) acc ->
            if dn = 0 && dp = 0 then Some t else acc
          ) sub_gr.eset None |> Option.value ~default:0 in
          let ty = try TM.find ty_id tm |> c_type_of_if1_ty tm with _ -> C.Basic "float" in
          Some ({ C.return_ty = ty; name = func_name; params; body = body @ [C.Return (Some e)]; extern_c = true }, None)
      else Some ({ C.return_ty = C.Void; name = func_name; params; body; extern_c = true }, None)
  | _ -> None

let translate (gr : graph) : C.translation_unit =
  let _, tm, _ = gr.typemap in
  let results = NM.fold (fun id node acc ->
    match lower_procedure tm id node with
    | Some r -> r :: acc
    | None -> acc
  ) gr.nmap [] in
  let procedures = List.map fst results in
  let result_struct_decls = List.filter_map snd results |> List.map (fun (name, fields) ->
      C.Decl (C.Struct (name, fields), "", None)) in
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
    includes = ["stdio.h"; "stdint.h"; "stdbool.h"; "dispatch/dispatch.h"; "Accelerate/Accelerate.h"; "sisal_runtime.h"];
    globals = record_structs @ result_struct_decls;
    procedures;
  }
