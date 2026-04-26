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
  (* ABS *)
  | "_SABS__F__F" -> Some "fabsf"
  | "_SABS__D__D" -> Some "fabs"
  | "_SABS__I__I" -> Some "abs"
  | "_SABS__L__L" -> Some "labs"
  (* SQRT / SQRTR *)
  | "_SSQRT__F__F" -> Some "sqrtf"
  | "_SSQRT__D__D" -> Some "sqrt"
  | "_SSQRTR__F__F" -> Some "sqrtf"
  | "_SSQRTR__D__D" -> Some "sqrt"
  (* SIN *)
  | "_SSIN__F__F" -> Some "sinf"
  | "_SSIN__D__D" -> Some "sin"
  (* COS *)
  | "_SCOS__F__F" -> Some "cosf"
  | "_SCOS__D__D" -> Some "cos"
  (* TAN *)
  | "_STAN__F__F" -> Some "tanf"
  | "_STAN__D__D" -> Some "tan"
  (* ASIN *)
  | "_SASIN__F__F" -> Some "asinf"
  | "_SASIN__D__D" -> Some "asin"
  (* ACOS *)
  | "_SACOS__F__F" -> Some "acosf"
  | "_SACOS__D__D" -> Some "acos"
  (* ATAN — 1-arg and 2-arg forms *)
  | "_SATAN__F__F" -> Some "atanf"
  | "_SATAN__D__D" -> Some "atan"
  | "_SATAN__FF__F" -> Some "atan2f"
  | "_SATAN__DD__D" -> Some "atan2"
  (* SINH / COSH / TANH *)
  | "_SSINH__F__F" -> Some "sinhf"
  | "_SSINH__D__D" -> Some "sinh"
  | "_SCOSH__F__F" -> Some "coshf"
  | "_SCOSH__D__D" -> Some "cosh"
  | "_STANH__F__F" -> Some "tanhf"
  | "_STANH__D__D" -> Some "tanh"
  (* LOG / LOG10 *)
  | "_SLOG__F__F" -> Some "logf"
  | "_SLOG__D__D" -> Some "log"
  | "_SLOG10__F__F" -> Some "log10f"
  | "_SLOG10__D__D" -> Some "log10"
  (* EXP (ETOTHE) *)
  | "_SETOTHE__F__F" -> Some "expf"
  | "_SETOTHE__D__D" -> Some "exp"
  (* FLOOR — returns integer type; cast baked into name *)
  | "_SFLOOR__F__I" -> Some "(int32_t)floorf"
  | "_SFLOOR__D__L" -> Some "(int64_t)floor"
  | "_SFLOOR__H__S" -> Some "(int16_t)floorf"
  (* TRUNC — same pattern *)
  | "_STRUNC__F__I" -> Some "(int32_t)truncf"
  | "_STRUNC__D__L" -> Some "(int64_t)trunc"
  | "_STRUNC__H__S" -> Some "(int16_t)truncf"
  (* RADIANS / DEGREES — defined as inline helpers in sisal_runtime.h *)
  | "_SRADIANS__F__F" -> Some "sisal_radians_f"
  | "_SRADIANS__D__D" -> Some "sisal_radians_d"
  | "_SDEGREES__F__F" -> Some "sisal_degrees_f"
  | "_SDEGREES__D__D" -> Some "sisal_degrees_d"
  | _ -> None

(** [lower_graph env gr gid] translates an IF1 graph into a list of C
    statements. It performs several steps: 1. Populates predecessor mappings for
    dataflow analysis. 2. Maps and initializes boundary inputs (params/incoming
    edges). 3. Pre-declares boundary output variables. 4. Topologically sorts
    nodes and lowers each node in order. 5. Propagates results to the boundary
    outputs. *)
let rec lower_graph env gr gid =
  let env_ref = ref { env with curr_gid = gid; curr_gr = gr } in
  let agreement_body = ref [] in

  (* 1. Populate preds from local edges *)
  let preds =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) m ->
        FullPortMap.add (gid, dn, dp, `In) (gid, sn, sp, `Out) m)
      gr.eset !env_ref.preds
  in
  env_ref := { !env_ref with preds };

  (* Boundary input parameters (node 0 Out ports) are already wired into
     var_map by lower_procedure (for functions) or by the parent lower_node
     (for compound subgraphs) using `Out direction.  No step needed here —
     adding `In aliases would collide with the result-variable slot below. *)

  (* Pre-declare boundary outputs (node 0 In ports).
     Use both the outs metadata list and actual incoming edges for robustness. *)
  let b_outs_from_metadata =
    match NM.find_opt 0 gr.nmap with
    | Some (Boundary (_, outs, errs, _)) ->
        let regular_outs = List.mapi (fun i _ -> i) outs in
        let error_outs = List.mapi (fun i _ -> List.length outs + i) errs in
        regular_outs @ error_outs
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
      let local_res_v = var_name gid 0 pid `In in
      (* Skip if the caller already pre-wired this boundary-out (e.g. LET output
       redirected to an outer variable so the inner scope writes directly). *)
      if FullPortMap.mem (gid, 0, pid, `In) !env_ref.var_map then ()
      else begin
        let ty = get_port_type !env_ref gr 0 pid `In in
        agreement_body := C.Decl (ty, local_res_v, None) :: !agreement_body;
        env_ref :=
          {
            !env_ref with
            var_map =
              FullPortMap.add (gid, 0, pid, `In) (C.Id local_res_v)
                !env_ref.var_map;
          }
      end)
    all_b_outs;

  (* 3. Computation block.
     If the graph contains a SELECT node it IS an IF compound (PREDICATE/BODY/ELSE graph).
     Delegate to lower_if_graph which emits a proper if/else, writing directly to the
     boundary-out vars pre-declared above.  Otherwise use the normal topo-sorted path. *)
  let res_stmts, final_env =
    let has_select =
      NM.exists
        (fun _ n ->
          match n with Simple (_, SELECT, _, _, _) -> true | _ -> false)
        gr.nmap
    in
    if has_select && Option.is_some (find_subgraph gr "PREDICATE") then
      let stmts, e = lower_if_graph !env_ref gr gid in
      (stmts, e)
    else begin
      let inner_decls = ref [] in
      let seen_decls = Hashtbl.create 16 in
      NM.iter
        (fun nid node ->
          if nid <> 0 then (
            let out_pids =
              match node with
              | Simple (_, _, _, pout, _) | Literal (_, _, _, pout) ->
                  let from_pout = List.init (Array.length pout) (fun i -> i) in
                  if from_pout <> [] then from_pout
                  else
                    ES.fold
                      (fun ((sn, sp), _, _) acc ->
                        if sn = nid then sp :: acc else acc)
                      gr.eset []
              | Compound (_, _, _, _, sub_gr, _) ->
                  let from_sub =
                    ES.fold
                      (fun (_, (dn, dp), _) acc ->
                        if dn = 0 then dp :: acc else acc)
                      sub_gr.eset []
                  in
                  if from_sub <> [] then from_sub
                  else
                    ES.fold
                      (fun ((sn, sp), _, _) acc ->
                        if sn = nid then sp :: acc else acc)
                      gr.eset []
              | _ -> [ 0 ]
            in
            let in_pids =
              match node with
              | Simple (_, _, pin, _, _) ->
                  List.init (Array.length pin) (fun i -> i)
              | Compound _ ->
                  ES.fold
                    (fun (_, (dn, dp), _) acc ->
                      if dn = nid then dp :: acc else acc)
                    gr.eset []
              | _ -> []
            in
            let tag =
              match node with
              | Simple (_, sym, _, _, _) ->
                  sanitize (Ir.If1.string_of_node_sym sym)
              | Literal _ -> "lit"
              | Compound (_, sym, _, pr, _, _) ->
                  let s = sanitize (Ir.If1.string_of_node_sym sym) in
                  if s = "" then
                    List.find_map
                      (function Name n -> Some (sanitize n) | _ -> None)
                      pr
                    |> Option.value ~default:"comp"
                  else s
              | _ -> ""
            in
            List.iter
              (fun pid ->
                let v = var_name ~tag gid nid pid `Out in
                if not (Hashtbl.mem seen_decls v) then (
                  Hashtbl.add seen_decls v ();
                  let ty =
                    match node with
                    | Simple (_, RANGEGEN, _, _, _) -> C.Basic "int32_t"
                    | Compound (_, _, _, pr, _, _)
                      when List.exists
                             (function Name n -> n = "FORALL" | _ -> false)
                             pr ->
                        C.Basic "sisal_array_t"
                    | Boundary _ when nid = 0 ->
                        get_port_type !env_ref gr 0 pid `Out
                    | _ -> get_port_type !env_ref gr nid pid `Out
                  in
                  inner_decls := C.Decl (ty, v, None) :: !inner_decls;
                  env_ref :=
                    {
                      !env_ref with
                      var_map =
                        FullPortMap.add (gid, nid, pid, `Out) (C.Id v)
                          !env_ref.var_map;
                    }))
              (List.sort_uniq compare out_pids);
            List.iter
              (fun pid ->
                let v = var_name ~tag gid nid pid `In in
                if not (Hashtbl.mem seen_decls v) then (
                  Hashtbl.add seen_decls v ();
                  let ty =
                    match node with
                    | Simple (_, RANGEGEN, _, _, _) -> C.Basic "int32_t"
                    | _ -> get_port_type !env_ref gr nid pid `In
                  in
                  inner_decls := C.Decl (ty, v, None) :: !inner_decls;
                  env_ref :=
                    {
                      !env_ref with
                      var_map =
                        FullPortMap.add (gid, nid, pid, `In) (C.Id v)
                          !env_ref.var_map;
                    }))
              (List.sort_uniq compare in_pids)))
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
                    ES.filter (fun (_, (dn, _), _) -> dn = nid) gr.eset
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
                  let node_stmts, next_env = lower_node !env_ref gr nid node in
                  env_ref := next_env;
                  acc @ node_stmts
              | None -> acc)
          [] topo_sorted
      in

      let propagation =
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = 0 then
              let src = get_expr !env_ref gid sn sp `Out in
              (* Use var_map for dst: a LET compound may have redirected the
             boundary-out to a caller-supplied variable (e.g. the outer
             function's result var), so honour that mapping. *)
              let dst =
                FullPortMap.find_opt (gid, 0, dp, `In) !env_ref.var_map
                |> Option.value
                     ~default:(C.Id (var_name ~tag:"graph_res" gid 0 dp `In))
              in
              C.Expr (C.BinOp (C.Assign, dst, src)) :: acc
            else acc)
          gr.eset []
      in

      ([ C.Compound (List.rev !inner_decls @ stmts @ propagation) ], !env_ref)
    end
  in
  let final_stmts = List.rev !agreement_body @ res_stmts in
  (final_stmts, final_env)

(** [lower_node env gr nid node] dispatches the lowering of an IF1 node to
    specialized functions for simple or compound nodes. *)
and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, _ty, pr, loop_gr, _assoc) ->
      let sub_gid = alloc_gid env.gid_table env.curr_gid cid in
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
      let is_for_initial =
        sy = INTERNAL
        && List.exists
             (function
               | Name n -> contains_substr (String.uppercase_ascii n) "LOOP"
               | _ -> false)
             pr
      in
      if is_real_forall then
        lower_forall env gr gid nid cid loop_gr sub_gid var_map_child pr
      else if is_for_initial then
        lower_for_initial env gr gid nid cid loop_gr sub_gid var_map_child
      else
        (* Generic transparent compound (e.g. LET_NON_REC or IF-container).
           Two extra wiring steps that FORALL/LOOP handle via their own logic:

           1. Output redirect: for each output edge (cid:sp -> outer), map the
              compound's inner boundary-out port sp to the pre-declared outer
              variable, so the inner lower_graph writes directly to it and the
              outer propagation step finds the right expr.

           2. Input fallback: if no explicit outer edges feed this compound
              (LET captures environment implicitly), wire its boundary inputs
              from the outer boundary by matching port index. *)
        let var_map_child =
          ES.fold
            (fun ((sn, sp), _, _) vm ->
              if sn = cid then
                let expr = get_expr env gid nid sp `In in
                FullPortMap.add (sub_gid, 0, sp, `Out) expr vm
              else vm)
            gr.eset var_map_child
        in
        let has_outer_edges =
          ES.exists (fun (_, (dn, _), _) -> dn = cid) gr.eset
        in
        let var_map_child =
          if not has_outer_edges then
            match NM.find_opt 0 loop_gr.nmap with
            | Some (Boundary (ins, _, _, _)) ->
                (* Wire each named boundary input to the variable it names.
                   Named captures in LET/IF come from GLOBAL-SYM, so the C
                   identifier is just the sanitized name already in scope. *)
                List.fold_left
                  (fun vm (_, pid, name) ->
                    let sname = sanitize name in
                    if sname = "" then vm
                    else
                      let expr = C.Id sname in
                      FullPortMap.add (sub_gid, 0, pid, `Out) expr vm)
                  var_map_child ins
            | _ -> var_map_child
          else var_map_child
        in
        let stmts, env_after_sub =
          lower_graph
            { env with var_map = var_map_child; parent_env = Some env }
            loop_gr sub_gid
        in

        (* 4. Propagate results from sub-graph boundary back to compound node outputs in parent *)
        let out_pids =
          ES.fold
            (fun ((sn, sp), _, _) acc -> if sn = cid then sp :: acc else acc)
            gr.eset []
        in
        let result_propagation =
          List.map
            (fun pid ->
              let src = get_expr env_after_sub sub_gid 0 pid `In in
              let dst = get_expr env gid cid pid `Out in
              C.Expr (C.BinOp (C.Assign, dst, src)))
            (List.sort_uniq compare out_pids)
        in

        (stmts @ result_propagation, env_after_sub)
  | Simple (_, sym, pin, pout, pr) ->
      (lower_simple env gr nid sym pin pout pr, env)
  | Literal (_, code, value, _pout) ->
      let v_res = get_expr env gid nid 0 `Out in
      let lit =
        try
          match code with
          | REAL | DOUBLE -> C.LitFloat (float_of_string value)
          | BOOLEAN -> C.Id (String.lowercase_ascii value)
          | _ -> C.LitInt (int_of_string value)
        with _ -> C.LitInt 0
      in
      ([ C.Expr (C.BinOp (C.Assign, v_res, lit)) ], env)
  | _ -> ([], env)

(** [lower_simple env gr nid sym pin pout pr] lowers a simple IF1 node (e.g.,
    math op, array access, select) into C expressions and statements. *)
and lower_simple env gr nid sym pin pout pr =
  let gid = env.curr_gid in
  let binop_opt =
    match sym with
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
    | OR -> Some C.LogOr
    | AND -> Some C.LogAnd
    | SHL -> Some C.Shl
    | SHR | ASHR -> Some C.Shr
    | _ -> None
  in
  match binop_opt with
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
      else if sym = NEGATE then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.UnaryOp (C.Negate, e))) ]
      else if sym = NOT then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.UnaryOp (C.LogNot, e))) ]
      else if sym = DV_ELEMENT || sym = AELEMENT then
        let arr = get_expr env env.curr_gid nid 0 `In in
        let idx = get_expr env env.curr_gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        (* Get element type from the INPUT array type (dn=nid, dp=0), not the
           scalar output (get_elem_type looks at sn=nid which gives the scalar). *)
        let arr_ty_id =
          let from_edges =
            ES.fold
              (fun ((_, _), (dn, dp), t) acc ->
                if dn = nid && dp = 0 && t <> 0 then Some t else acc)
              gr.eset None
          in
          match from_edges with
          | Some t -> t
          | None -> (
              (* Fallback: search parents if this is a nested compound like BODY *)
              match env.parent_env with
              | Some p_env -> (
                  let match_found =
                    FullPortMap.fold
                      (fun (g, n, p, dir) expr acc ->
                        if dir = `Out && expr = arr then
                          let ty = get_port_type p_env p_env.curr_gr n p dir in
                          Some ty
                        else acc)
                      p_env.var_map None
                  in
                  match match_found with
                  | Some (C.Basic "sisal_array_t") ->
                      111 (* dummy array_dv ID *)
                  | _ -> 0)
              | None -> 0)
        in
        let elem_ty =
          try
            match TM.find arr_ty_id env.tm with
            | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm
            | _ -> Unknown_ty
          with _ -> Unknown_ty
        in
        let cast_ty =
          match c_type_of_if1_ty env.tm elem_ty with
          | C.Basic "void*" | C.Basic "float" ->
              (* Final heuristic fallback based on input names or surrounding context *)
              if arr = C.Id "a" || arr = C.Id "b" then "float" else "float"
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
      else if sym = ALIML then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               ( C.Assign,
                 v_res,
                 C.Cast (C.Basic "int32_t", C.Member (arr, "lower_bound")) ));
        ]
      else if sym = ALIMH then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               ( C.Assign,
                 v_res,
                 C.BinOp
                   ( C.Sub,
                     C.BinOp
                       ( C.Add,
                         C.Member (arr, "lower_bound"),
                         C.Member (arr, "size") ),
                     C.LitInt 1 ) ));
        ]
      else if sym = AREML || sym = AREMH || sym = AADDL then
        failwith
          (Printf.sprintf
             "lower_simple: traditional Sisal array node %s is not supported \
              in the Silicon/DV backend (nid=%d)"
             (Ir.If1.string_of_node_sym sym)
             nid)
      else if sym = ASETL then
        let arr = get_expr env gid nid 0 `In in
        let lb = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr (C.BinOp (C.Assign, v_res, arr));
          C.Expr
            (C.BinOp
               ( C.Assign,
                 C.Member (v_res, "lower_bound"),
                 C.Cast (C.Basic "int64_t", lb) ));
        ]
      else if sym = DV_CREATE then
        let lb = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let tid =
          match get_elem_type env gr nid with
          | Basic REAL -> 0
          | Basic DOUBLE -> 1
          | Basic INTEGRAL -> 2
          | Basic BOOLEAN -> 3
          | _ -> 0
        in
        let in_edges_count =
          ES.fold
            (fun (_, (dn, _), _) acc -> if dn = nid then acc + 1 else acc)
            gr.eset 0
        in
        let core_stmts =
          if in_edges_count = 3 then
            let size_or_ub = get_expr env gid nid 1 `In in
            let val_ = get_expr env gid nid 2 `In in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     v_res,
                     C.Call ("sisal_array_fill", [ lb; size_or_ub; val_ ]) ));
            ]
          else
            let size = get_expr env gid nid 1 `In in
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
        in
        let err_stmts =
          if Array.length pout > 1 then
            let v_err = get_expr env gid nid 1 `Out in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     v_err,
                     C.BinOp (C.Eq, C.Member (v_res, "data"), C.LitInt 0) ));
            ]
          else []
        in
        core_stmts @ err_stmts
      else if sym = ACREATE then
        let lb = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let tid =
          match get_elem_type env gr nid with
          | Basic REAL -> 0
          | Basic DOUBLE -> 1
          | Basic INTEGRAL -> 2
          | Basic BOOLEAN -> 3
          | _ -> 0
        in
        let core_stmts =
          [
            C.Expr
              (C.BinOp
                 ( C.Assign,
                   v_res,
                   C.Call
                     ( "sisal_array_alloc_empty",
                       [ C.LitInt 1; C.LitInt tid; C.LitInt 0 ] ) ));
            C.Expr (C.BinOp (C.Assign, C.Member (v_res, "lower_bound"), lb));
          ]
        in
        let err_stmts =
          if Array.length pout > 1 then
            let v_err = get_expr env gid nid 1 `Out in
            [
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     v_err,
                     C.BinOp (C.Eq, C.Member (v_res, "data"), C.LitInt 0) ));
            ]
          else []
        in
        core_stmts @ err_stmts
      else if sym = AREPLACE || sym = DV_REPLACE then
        let arr = get_expr env gid nid 0 `In in
        let idx = get_expr env gid nid 1 `In in
        let val_ = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               ( C.Assign,
                 v_res,
                 C.Call ("sisal_array_replace", [ arr; idx; val_ ]) ));
        ]
      else if sym = SELECT then
        let cond = get_expr env gid nid 0 `In in
        let v_then = get_expr env gid nid 1 `In in
        let v_else = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Cond (cond, v_then, v_else))) ]
      else if sym = FINALVALUE || sym = AGATHER then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, e)) ]
      else if sym = SHAPE_CHECK then
        (* No-op for now, or could call a runtime check *)
        []
      else if sym = CONCAT_NODE || sym = ACATENATE then
        let a = get_expr env gid nid 0 `In in
        let b = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_concat", [ a; b ])));
        ]
      else if sym = AFILL || sym = MATSPLAT || sym = VSPLAT then
        let lb = get_expr env gid nid 0 `In in
        let size = get_expr env gid nid 1 `In in
        let val_ = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_fill", [ lb; size; val_ ])));
        ]
      else if sym = ASCATTER then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, e)) ]
      else if sym = REDUCE_AXIS then
        let arr = get_expr env gid nid 0 `In in
        let axis = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               ( C.Assign,
                 v_res,
                 C.Call ("sisal_array_reduce_axis", [ arr; axis ]) ));
        ]
      else if sym = MAP_NODE then
        let f = get_expr env gid nid 0 `In in
        let arr = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_map", [ f; arr ])));
        ]
      else if sym = FOLDL_NODE || sym = FOLDR_NODE then
        let f = get_expr env gid nid 0 `In in
        let init = get_expr env gid nid 1 `In in
        let arr = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let func =
          if sym = FOLDL_NODE then "sisal_array_foldl" else "sisal_array_foldr"
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func, [ f; init; arr ]))) ]
      else if sym = SCAN_NODE then
        let f = get_expr env gid nid 0 `In in
        let arr = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_scan", [ f; arr ])));
        ]
      else if sym = DV_PERMUTE then
        let arr = get_expr env gid nid 0 `In in
        let dims = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_permute", [ arr; dims ])));
        ]
      else if sym = DV_ROTATE then
        let arr = get_expr env gid nid 0 `In in
        let n = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_rotate", [ arr; n ])));
        ]
      else if sym = DV_REVERSE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_reverse", [ arr ])));
        ]
      else if sym = RAVEL_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_ravel", [ arr ])));
        ]
      else if sym = DV_COMPRESS then
        let mask = get_expr env gid nid 0 `In in
        let arr = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_compress", [ mask; arr ])));
        ]
      else if sym = DV_SORT then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_sort", [ arr ])));
        ]
      else if sym = DV_GRADE_UP || sym = DV_GRADE_DOWN then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let func =
          if sym = DV_GRADE_UP then "sisal_array_grade_up"
          else "sisal_array_grade_down"
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func, [ arr ]))) ]
      else if sym = DV_OUTERPRODUCT then
        let f = get_expr env gid nid 0 `In in
        let a = get_expr env gid nid 1 `In in
        let b = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               ( C.Assign,
                 v_res,
                 C.Call ("sisal_array_outerproduct", [ f; a; b ]) ));
        ]
      else if sym = INNERPRODUCT_NODE then
        let a = get_expr env gid nid 0 `In in
        let b = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_innerproduct", [ a; b ])));
        ]
      else if sym = ARGMAX_NODE || sym = ARGMIN_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let func =
          if sym = ARGMAX_NODE then "sisal_array_argmax"
          else "sisal_array_argmin"
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func, [ arr ]))) ]
      else if sym = MEAN_NODE || sym = VARIANCE_NODE || sym = STDDEV_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let func =
          match sym with
          | MEAN_NODE -> "sisal_array_mean"
          | VARIANCE_NODE -> "sisal_array_variance"
          | _ -> "sisal_array_stddev"
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func, [ arr ]))) ]
      else if sym = ANY_NODE || sym = ALL_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let func =
          if sym = ANY_NODE then "sisal_array_any" else "sisal_array_all"
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func, [ arr ]))) ]
      else if sym = NORM_NODE then
        let arr = get_expr env gid nid 0 `In in
        let p = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_norm", [ arr; p ])));
        ]
      else if sym = NONZERO_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_nonzero", [ arr ])));
        ]
      else if sym = WHERE_NODE then
        let cond = get_expr env gid nid 0 `In in
        let x = get_expr env gid nid 1 `In in
        let y = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_where", [ cond; x; y ])));
        ]
      else if sym = CUMSUM_NODE || sym = CUMPROD_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let func =
          if sym = CUMSUM_NODE then "sisal_array_cumsum"
          else "sisal_array_cumprod"
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func, [ arr ]))) ]
      else if sym = TILE_NODE then
        let arr = get_expr env gid nid 0 `In in
        let n = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_tile", [ arr; n ])));
        ]
      else if sym = SQUEEZE_NODE then
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_squeeze", [ arr ])));
        ]
      else if sym = EXPAND_NODE then
        let arr = get_expr env gid nid 0 `In in
        let k = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_expand", [ arr; k ])));
        ]
      else if sym = STENCIL_NODE then
        let f = get_expr env gid nid 0 `In in
        let arr = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_stencil", [ f; arr ])));
        ]
      else if sym = PAD_NODE then
        let arr = get_expr env gid nid 0 `In in
        let lo = get_expr env gid nid 1 `In in
        let hi = get_expr env gid nid 2 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_pad", [ arr; lo; hi ])));
        ]
      else if sym = REDUCE_ALL then
        let op_str =
          match pr with Name s :: _ -> String.lowercase_ascii s | _ -> "sum"
        in
        let arg = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let ty_id =
          ES.fold
            (fun (_, (dn, dp), t) acc ->
              if dn = nid && dp = 0 && t <> 0 then Some t else acc)
            gr.eset None
          |> Option.value ~default:0
        in
        let ty = try TM.find ty_id env.tm with _ -> Unknown_ty in
        let c_ty = c_type_of_if1_ty env.tm ty in
        let prefix =
          if c_ty = C.Basic "float" then "sisal_array_reduce_"
          else if c_ty = C.Basic "double" then "sisal_array_reduce_double_"
          else "sisal_array_reduce_int_"
        in
        let call = C.Call (prefix ^ op_str, [ arg ]) in
        let final_expr =
          if prefix = "sisal_array_reduce_int_" then
            C.Cast (C.Basic "int32_t", call)
          else call
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, final_expr)) ]
      else if sym = INVOCATION then
        let func_name =
          let raw =
            List.find_map (function Name s -> Some s | _ -> None) pr
            |> Option.value ~default:(Printf.sprintf "func_%d" nid)
          in
          Option.value (c_name_of_mangled raw) ~default:raw
        in
        (* Count input ports by checking edges or using ports array if available.
           Actually, get_expr handles the lookup. We need to know how many. *)
        let in_edges =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid then IntSet.add dp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let args =
          List.map (fun pid -> get_expr env gid nid pid `In) in_edges
        in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Call (func_name, args))) ]
      else if sym = ABUILD then
        let in_edges =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid then IntSet.add dp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let args =
          List.map (fun pid -> get_expr env gid nid pid `In) in_edges
        in
        let v_res = get_expr env gid nid 0 `Out in
        (* ABUILD needs LB, type_id, count, and then elements.
           Assume LB=1, type_id=0 for now, or get from edges. *)
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
                     C.LitInt 1 :: C.LitInt tid
                     :: C.LitInt (List.length args)
                     :: args ) ));
        ]
      else if sym = AADDH then
        let arr = get_expr env gid nid 0 `In in
        let val_ = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               (C.Assign, v_res, C.Call ("sisal_array_addh", [ arr; val_ ])));
        ]
      else if sym = DOT then
        let a = get_expr env gid nid 0 `In in
        let b = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp (C.Assign, v_res, C.Call ("sisal_array_dot", [ a; b ])));
        ]
      else if sym = ERROR_NODE then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, e)) ]
      else if sym = DV_NUM_RANK then
        let ty_id =
          ES.fold
            (fun ((sn, sp), _, t) acc ->
              if sn = nid && sp = 0 && t <> 0 then Some t else acc)
            gr.eset None
          |> Option.value ~default:0
        in
        let ty = try TM.find ty_id env.tm with _ -> Unknown_ty in
        let arr = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        match ty with
        | Array_dv _ | Array_ty _ ->
            [ C.Expr (C.BinOp (C.Assign, v_res, C.Member (arr, "rank"))) ]
        | _ -> [ C.Expr (C.BinOp (C.Assign, v_res, C.LitInt 0)) ]
      else if sym = DV_OFFSET_AT then
        let v_res = get_expr env gid nid 0 `Out in
        (* Stub: return 0 for now until full multi-dim offset logic is added *)
        [ C.Expr (C.BinOp (C.Assign, v_res, C.LitInt 0)) ]
      else if sym = DV_LOAD_LINEAR then
        let arr = get_expr env gid nid 0 `In in
        let off = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        let cast_ptr =
          C.Cast (C.Pointer (C.Basic "float", []), C.Member (arr, "data"))
        in
        [ C.Expr (C.BinOp (C.Assign, v_res, C.Index (cast_ptr, off))) ]
      else if sym = DV_RESHAPE_BY_SHAPE then
        let arr = get_expr env gid nid 0 `In in
        let sh = get_expr env gid nid 1 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [
          C.Expr
            (C.BinOp
               ( C.Assign,
                 v_res,
                 C.Call ("sisal_array_reshape_by_shape", [ arr; sh ]) ));
        ]
      else if sym = DV_SCATTER || sym = DV_GATHER then
        let e = get_expr env gid nid 0 `In in
        let v_res = get_expr env gid nid 0 `Out in
        [ C.Expr (C.BinOp (C.Assign, v_res, e)) ]
      else if sym = RELEMENTS then
        let rec_expr = get_expr env gid nid 1 `In in
        List.init (Array.length pout) (fun i ->
            let v_res = get_expr env gid nid i `Out in
            let field_name =
              if i < Array.length pin then pin.(i)
              else if i = 0 then pin.(0)
              else "f"
            in
            (* If Port 0 was used for metadata, and we have one output, use pin.(0) *)
            let field_name =
              if Array.length pout = 1 && Array.length pin > 0 then pin.(0)
              else field_name
            in
            C.Expr (C.BinOp (C.Assign, v_res, C.Member (rec_expr, field_name))))
      else if sym = RBUILD then
        List.init (Array.length pin) (fun i ->
            let arg = get_expr env gid nid i `In in
            let field_name = pin.(i) in
            let v_res = get_expr env gid nid 0 `Out in
            C.Expr (C.BinOp (C.Assign, C.Member (v_res, field_name), arg)))
      else
        let sym_str = Ir.If1.string_of_node_sym sym in
        failwith
          (Printf.sprintf "lower_simple: node type not implemented: %s (nid=%d)"
             sym_str nid)

(* lower_if_graph: lower a graph that IS an IF compound.
   Called by lower_graph when it detects a SELECT node.
   Boundary inputs and pre-declared boundary-out vars are already in env.var_map
   (set up by lower_graph steps 2&3 before this call).
   SELECT absorption writes directly to those pre-declared boundary-out vars. *)
and lower_if_graph env gr gid =
  let wire_inputs child_cid child_gid base_vm =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) m ->
        if dn = child_cid then
          FullPortMap.add (child_gid, 0, dp, `Out)
            (get_expr env gid sn sp `Out)
            m
        else m)
      gr.eset base_vm
  in
  let register_child_outputs child_cid child_gid child_env base_env =
    ES.fold
      (fun ((sn, sp), _, _) e ->
        if sn = child_cid then
          let expr = get_expr child_env child_gid 0 sp `In in
          {
            e with
            var_map = FullPortMap.add (gid, child_cid, sp, `In) expr e.var_map;
          }
        else e)
      gr.eset
      { base_env with curr_gid = gid }
  in

  (* 0. Pre-declare Bridge Variables for PREDICATE results *)
  let pred_cid, _ =
    match find_subgraph gr "PREDICATE" with
    | Some x -> x
    | _ -> failwith "no PRED"
  in
  let pgid = alloc_gid env.gid_table gid pred_cid in
  let pred_bridge_v = var_name ~tag:"pred" gid pred_cid 0 `In in
  let pred_decl = C.Decl (C.Basic "bool", pred_bridge_v, None) in
  (* IMPORTANT: Register the bridge variable as the target for the subgraph's boundary-out at port 0 *)
  let env_with_pred_bridge =
    {
      env with
      var_map =
        FullPortMap.add (pgid, 0, 0, `In) (C.Id pred_bridge_v) env.var_map;
    }
  in

  (* 1. Lower PREDICATE *)
  let pred_stmts, pred_env =
    let vm = wire_inputs pred_cid pgid env_with_pred_bridge.var_map in
    let stmts, e' =
      lower_graph
        { env_with_pred_bridge with var_map = vm }
        (match find_subgraph gr "PREDICATE" with
        | Some (_, g) -> g
        | _ -> assert false)
        pgid
    in
    (stmts, e')
  in
  let pred_expr = C.Id pred_bridge_v in
  let env1 = register_child_outputs pred_cid pgid pred_env env in

  (* 2. Lower BODY (then-branch) *)
  let body_stmts, body_gid, body_cid, body_env_raw =
    match find_subgraph gr "BODY" with
    | None -> failwith "lower_if_graph: no BODY"
    | Some (bcid, bgr) ->
        let bgid = alloc_gid env.gid_table gid bcid in
        let vm = wire_inputs bcid bgid env1.var_map in
        let stmts, e' = lower_graph { env1 with var_map = vm } bgr bgid in
        (stmts, bgid, bcid, e')
  in
  let body_env_m =
    ES.fold
      (fun ((sn, sp), _, _) m ->
        if sn = body_cid then
          let expr = get_expr body_env_raw body_gid 0 sp `In in
          FullPortMap.add (gid, body_cid, sp, `In) expr m
        else m)
      gr.eset body_env_raw.var_map
  in
  let body_env = { body_env_raw with var_map = body_env_m; curr_gid = gid } in

  (* 3. Lower ELSE branch; if it also has SELECT, lower_graph recurses into lower_if_graph *)
  let else_stmts, else_gid, else_cid, else_env_raw =
    match find_subgraph gr "ELSE" with
    | None -> failwith "lower_if_graph: no ELSE"
    | Some (ecid, egr) ->
        let egid = alloc_gid env.gid_table gid ecid in
        let vm = wire_inputs ecid egid env1.var_map in
        let stmts, e' = lower_graph { env1 with var_map = vm } egr egid in
        (stmts, egid, ecid, e')
  in
  let else_env_m =
    ES.fold
      (fun ((sn, sp), _, _) m ->
        if sn = else_cid then
          let expr = get_expr else_env_raw else_gid 0 sp `In in
          FullPortMap.add (gid, else_cid, sp, `In) expr m
        else m)
      gr.eset else_env_raw.var_map
  in
  let else_env = { else_env_raw with var_map = else_env_m; curr_gid = gid } in

  (* 4. Absorb SELECT: assign branch results into the pre-declared boundary-out vars *)
  let sel_infos = find_boundary_selects gr in

  (* 5. Error Propagation from Subgraphs *)
  let pred_errs = get_subgraph_errors env gid pred_cid in
  let body_errs = get_subgraph_errors body_env gid body_cid in
  let else_errs = get_subgraph_errors else_env gid else_cid in

  (* Map these back to the IF node's own error outputs (node 0 in current graph) *)
  let if_err_assigns_pred =
    List.mapi
      (fun i err_expr ->
        let pid = List.length sel_infos + i in
        let res_v =
          FullPortMap.find_opt (gid, 0, pid, `In) env.var_map
          |> Option.value ~default:(C.Id (var_name ~tag:"if_err" gid 0 pid `In))
        in
        C.Expr (C.BinOp (C.Assign, res_v, err_expr)))
      pred_errs
  in
  let if_err_assigns_then =
    List.mapi
      (fun i err_expr ->
        let pid = List.length sel_infos + i in
        let res_v =
          FullPortMap.find_opt (gid, 0, pid, `In) env.var_map
          |> Option.value ~default:(C.Id (var_name ~tag:"if_err" gid 0 pid `In))
        in
        C.Expr (C.BinOp (C.Assign, res_v, err_expr)))
      body_errs
  in
  let if_err_assigns_else =
    List.mapi
      (fun i err_expr ->
        let pid = List.length sel_infos + i in
        let res_v =
          FullPortMap.find_opt (gid, 0, pid, `In) env.var_map
          |> Option.value ~default:(C.Id (var_name ~tag:"if_err" gid 0 pid `In))
        in
        C.Expr (C.BinOp (C.Assign, res_v, err_expr)))
      else_errs
  in

  let then_assigns =
    List.filter_map
      (fun (sel_nid, bport) ->
        let res_v =
          FullPortMap.find_opt (gid, 0, bport, `In) env.var_map
          |> Option.value
               ~default:(C.Id (var_name ~tag:"if_res" gid 0 bport `In))
        in
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = sel_nid && dp = 1 then
              (* This input to SELECT comes from a subgraph output or current graph *)
              if sn = body_cid then
                let src = get_expr body_env body_gid 0 sp `In in
                Some (C.Expr (C.BinOp (C.Assign, res_v, src)))
              else
                let src = get_expr env gid sn sp `Out in
                Some (C.Expr (C.BinOp (C.Assign, res_v, src)))
            else acc)
          gr.eset None)
      sel_infos
  in
  let else_assigns =
    List.filter_map
      (fun (sel_nid, bport) ->
        let res_v =
          FullPortMap.find_opt (gid, 0, bport, `In) env.var_map
          |> Option.value
               ~default:(C.Id (var_name ~tag:"if_res" gid 0 bport `In))
        in
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = sel_nid && dp = 2 then
              (* This input to SELECT comes from a subgraph output or current graph *)
              if sn = else_cid then
                let src = get_expr else_env else_gid 0 sp `In in
                Some (C.Expr (C.BinOp (C.Assign, res_v, src)))
              else
                let src = get_expr env gid sn sp `Out in
                Some (C.Expr (C.BinOp (C.Assign, res_v, src)))
            else acc)
          gr.eset None)
      sel_infos
  in

  let if_core =
    [
      C.If
        ( pred_expr,
          body_stmts @ then_assigns @ if_err_assigns_then,
          else_stmts @ else_assigns @ if_err_assigns_else );
    ]
  in
  let implementation =
    (pred_decl :: pred_stmts)
    @
    if if_err_assigns_pred <> [] then
      let has_err = match pred_errs with [] -> C.LitInt 0 | e :: _ -> e in
      (* simplified check *)
      [ C.If (has_err, if_err_assigns_pred, if_core) ]
    else if_core
  in
  (* Combine environments from branches: take parent env then layer on updates *)
  let final_env =
    {
      env with
      var_map =
        FullPortMap.union
          (fun _ a _ -> Some a)
          body_env.var_map else_env.var_map;
    }
  in
  (implementation, final_env)

and lower_for_initial env gr gid nid _cid loop_gr sub_gid var_map_child =
  let env_init = { env with var_map = var_map_child; parent_env = Some env } in

  let init_info = find_subgraph loop_gr "INIT" in
  let test_info = find_subgraph loop_gr "TEST" in
  let body_info = find_subgraph loop_gr "BODY" in
  let ret_info = find_subgraph loop_gr "RETURNS" in

  match (init_info, test_info, body_info, ret_info) with
  | ( Some (init_nid, init_gr),
      Some (test_nid, test_gr),
      Some (body_nid, body_gr),
      Some (ret_nid, ret_gr) ) ->
      let init_gid = alloc_gid env.gid_table sub_gid init_nid in
      let test_gid = alloc_gid env.gid_table sub_gid test_nid in
      let body_gid = alloc_gid env.gid_table sub_gid body_nid in
      let ret_gid = alloc_gid env.gid_table sub_gid ret_nid in

      (* 1. Lower INIT *)
      let init_stmts, e_init = lower_graph env_init init_gr init_gid in
      (* 2. Map INIT outputs to their names from symtab *)
      let init_out_names =
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = 0 then
              match get_port_name init_gr sn sp `Out with
              | Some name -> IntMap.add dp name acc
              | None -> acc
            else acc)
          init_gr.eset IntMap.empty
      in

      (* 3. Declare mutable state variables for each INIT output *)
      let state_vars =
        IntMap.bindings init_out_names
        |> List.map (fun (pid, name) ->
            let v = Printf.sprintf "v_g%d_state_%s" sub_gid name in
            let ty = get_port_type e_init init_gr 0 pid `In in
            (pid, name, v, ty))
      in

      let init_decls =
        List.map
          (fun (pid, _name, v, ty) ->
            C.Decl (ty, v, Some (get_expr e_init init_gid 0 pid `In)))
          state_vars
      in

      (* Helper: wire a subgraph by matching boundary input names to state variables *)
      let wire_subgraph child_gid child_gr =
        let vm = ref var_map_child in
        match NM.find_opt 0 child_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.iter
              (fun (_ty, pid, name) ->
                let sname = sanitize name in
                if sname <> "" then
                  match
                    List.find_opt (fun (_, n, _, _) -> n = sname) state_vars
                  with
                  | Some (_, _, v, _) ->
                      vm :=
                        FullPortMap.add (child_gid, 0, pid, `Out) (C.Id v) !vm
                  | None -> ()
                else
                  match
                    List.find_opt (fun (p, _, _, _) -> p = pid) state_vars
                  with
                  | Some (_, _, v, _) ->
                      vm :=
                        FullPortMap.add (child_gid, 0, pid, `Out) (C.Id v) !vm
                  | None -> ())
              ins;
            !vm
        | _ -> !vm
      in

      (* 4. Lower TEST - feeds from current state variables *)
      let test_vm = wire_subgraph test_gid test_gr in
      let test_stmts, e_test =
        lower_graph { env_init with var_map = test_vm } test_gr test_gid
      in
      let test_expr = get_expr e_test test_gid 0 0 `In in

      (* 5. Lower BODY - feeds from current state variables *)
      let body_vm = wire_subgraph body_gid body_gr in
      let body_stmts, e_body =
        lower_graph { env_init with var_map = body_vm } body_gr body_gid
      in

      (* 6. Update state from BODY outputs by matching names *)
      let body_out_names =
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = 0 then
              match get_port_name body_gr sn sp `Out with
              | Some name -> IntMap.add dp name acc
              | None -> acc
            else acc)
          body_gr.eset IntMap.empty
      in

      let update_stmts = ref [] in
      List.iter
        (fun (_pid, name, v, _ty) ->
          let found = ref false in
          IntMap.iter
            (fun dp n ->
              if n = name then begin
                update_stmts :=
                  C.Expr
                    (C.BinOp
                       (C.Assign, C.Id v, get_expr e_body body_gid 0 dp `In))
                  :: !update_stmts;
                found := true
              end)
            body_out_names;
          if not !found then begin
            NM.iter
              (fun nid_ node ->
                if not !found then begin
                  match node with
                  | Simple (_, _, _, _, pr) | Compound (_, _, _, pr, _, _) ->
                      if
                        List.exists
                          (function Name s -> sanitize s = name | _ -> false)
                          pr
                      then begin
                        update_stmts :=
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 C.Id v,
                                 get_expr e_body body_gid nid_ 0 `Out ))
                          :: !update_stmts;
                        found := true
                      end
                  | _ -> ()
                end)
              body_gr.nmap
          end)
        state_vars;

      (* 7. Lower RETURNS *)
      let ret_vm = wire_subgraph ret_gid ret_gr in
      let ret_stmts, e_ret =
        lower_graph { env_init with var_map = ret_vm } ret_gr ret_gid
      in

      (* 8. Map final results to compound node outputs *)
      let res_assigns =
        let outs =
          match NM.find_opt 0 ret_gr.nmap with
          | Some (Boundary (_, o, _, _)) -> o
          | _ -> []
        in
        List.mapi
          (fun i _ ->
            let res_v = get_expr env gid nid i `Out in
            C.Expr (C.BinOp (C.Assign, res_v, get_expr e_ret ret_gid 0 i `In)))
          outs
      in

      ( init_stmts @ init_decls
        @ [
            C.While
              ( C.LitInt 1,
                test_stmts
                @ [ C.If (C.UnaryOp (C.LogNot, test_expr), [ C.Break ], []) ]
                @ body_stmts @ !update_stmts );
          ]
        @ ret_stmts @ res_assigns,
        env )
  | _ ->
      failwith
        "lower_for_initial: missing required subgraphs (INIT, TEST, BODY, \
         RETURNS)"

and lower_forall env gr gid nid _cid loop_gr sub_gid var_map_child _pr =
  (* FORALL subgraphs (GENERATOR, BODY, RETURNS) share scope via GLOBAL-SYM:
     loop_gr.eset is empty.  Wire each child's boundary inputs by matching port
     names against the FORALL boundary.  Then lower GENERATOR and BODY
     explicitly rather than running lower_graph on the whole loop_gr. *)

  (* Build (lowercase_name, expr) association list from FORALL boundary.
     Port IDs come from list position (List.rev because boundary entries are
     prepended); values are looked up with `In since lower_node stores them
     that way when wiring compound inputs. *)
  let forall_named_inputs =
    match NM.find_opt 0 loop_gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.rev ins
        |> List.mapi (fun pid (_, _, name) -> (pid, name))
        |> List.filter_map (fun (pid, name) ->
            let sname = String.lowercase_ascii name in
            if sname = "" then None
            else
              match
                FullPortMap.find_opt (sub_gid, 0, pid, `Out) var_map_child
              with
              | Some expr -> Some (sname, expr)
              | None -> None)
    | _ -> []
  in

  let forall_indexed_inputs =
    match NM.find_opt 0 loop_gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        List.rev ins
        |> List.mapi (fun pid _ ->
            match
              FullPortMap.find_opt (sub_gid, 0, pid, `Out) var_map_child
            with
            | Some expr -> Some (pid, expr)
            | None -> None)
        |> List.filter_map (fun x -> x)
    | _ -> []
  in

  (* Wire a child subgraph's boundary outputs (`Out) by name-matching or port ID. *)
  let wire_child child_gid child_gr =
    match NM.find_opt 0 child_gr.nmap with
    | Some (Boundary (ins, _, _, _)) ->
        let rev_ins = List.rev ins in
        List.fold_left
          (fun (vm, pid) (_, _, name) ->
            let sname = String.lowercase_ascii name in
            let expr_opt =
              if sname <> "" then List.assoc_opt sname forall_named_inputs
              else List.assoc_opt pid forall_indexed_inputs
            in
            let vm' =
              match expr_opt with
              | Some expr -> FullPortMap.add (child_gid, 0, pid, `Out) expr vm
              | None -> vm
            in
            (vm', pid + 1))
          (var_map_child, 0) rev_ins
        |> fst
    | _ -> var_map_child
  in

  (* 1. Lower GENERATOR. *)
  let gen_stmts, gen_env, count_expr, lo_expr =
    match find_subgraph loop_gr "GENERATOR" with
    | None ->
        ( [],
          { env with var_map = var_map_child; curr_gid = sub_gid },
          C.Id "0",
          C.LitInt 0 )
    | Some (gen_nid, gen_gr) ->
        let gen_gid = alloc_gid env.gid_table sub_gid gen_nid in
        let gen_vm = wire_child gen_gid gen_gr in
        let stmts, e' =
          lower_graph
            { env with var_map = gen_vm; parent_env = Some env }
            gen_gr gen_gid
        in
        (* count: boundary-out of GENERATOR — the port dp where dn=0 in gen_gr *)
        let count_bp =
          ES.fold
            (fun (_, (dn, dp), _) acc -> if dn = 0 then Some dp else acc)
            gen_gr.eset None
        in
        let has_rangegen =
          NM.exists
            (fun _ n ->
              match n with Simple (_, RANGEGEN, _, _, _) -> true | _ -> false)
            gen_gr.nmap
        in
        let count_expr =
          if has_rangegen then
            match count_bp with
            | Some dp -> C.Id (var_name gen_gid 0 dp `In)
            | None -> C.Id "0"
          else
            (* Array-based FORALL: count is size of the first input array *)
            match NM.find_opt 0 gen_gr.nmap with
            | Some (Boundary (ins, _, _, _)) ->
                let first_arr = get_expr e' gen_gid 0 0 `Out in
                C.Member (first_arr, "size")
            | _ -> (
                match count_bp with
                | Some dp -> C.Id (var_name gen_gid 0 dp `In)
                | None -> C.Id "0")
        in
        let lo =
          if has_rangegen then
            match List.assoc_opt "lo" forall_named_inputs with
            | Some expr -> expr
            | None ->
                NM.fold
                  (fun rgn_nid node acc ->
                    match node with
                    | Simple (_, RANGEGEN, _, _, _) ->
                        let src =
                          ES.fold
                            (fun ((sn, sp), (dn, dp), _) a ->
                              if dn = rgn_nid && dp = 0 then Some (sn, sp)
                              else a)
                            gen_gr.eset None
                        in
                        let res =
                          match src with
                          | None -> acc
                          | Some (sn, sp) -> (
                              match NM.find_opt sn gen_gr.nmap with
                              | Some (Literal (_, _, value, _)) -> (
                                  try C.LitInt (int_of_string value)
                                  with _ -> acc)
                              | _ -> get_expr e' gen_gid sn sp `Out)
                        in
                        res
                    | _ -> acc)
                  gen_gr.nmap (C.LitInt 0)
          else C.LitInt 0
        in
        (stmts, e', count_expr, lo)
  in

  (* 2. Allocate result array and set lower_bound *)
  let res_v = get_expr env gid nid 0 `Out in
  let elem_ty =
    match get_elem_type env gr nid with
    | Unknown_ty -> ( try TM.find 8 env.tm with _ -> Unknown_ty)
    | ty -> ty
  in
  let tid = type_id_of_if1_ty env.tm elem_ty in
  let cast_ty =
    match c_type_of_if1_ty env.tm elem_ty with C.Basic s -> s | _ -> "float"
  in

  let alloc_stmt =
    C.Expr
      (C.BinOp
         ( C.Assign,
           res_v,
           C.Call
             ( "sisal_array_alloc_empty",
               [
                 C.LitInt 1;
                 C.LitInt tid;
                 C.Cast (C.Basic "uint64_t", count_expr);
               ] ) ))
  in
  let lo_bound_stmt =
    C.Expr
      (C.BinOp
         ( C.Assign,
           C.Member (res_v, "lower_bound"),
           C.Cast (C.Basic "int64_t", lo_expr) ))
  in

  (* 3. Lower BODY inside dispatch_apply *)
  match find_subgraph loop_gr "BODY" with
  | None -> (gen_stmts @ [ alloc_stmt; lo_bound_stmt ], env)
  | Some (body_nid, body_gr) ->
      let body_gid = alloc_gid env.gid_table sub_gid body_nid in
      let index_var = Printf.sprintf "v_idx_g%d" body_gid in

      (* Wire BODY boundary outputs (`Out) by name; inject index for I/__lfi *)
      let body_vm = wire_child body_gid body_gr in
      let body_vm =
        match NM.find_opt 0 body_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.rev ins
            |> List.fold_left
                 (fun (vm, pid) (_, _, name) ->
                   let sname = String.lowercase_ascii name in
                   let vm' =
                     if sname = "i" || sname = "index" || sname = "__lfi" then
                       FullPortMap.add (body_gid, 0, pid, `Out)
                         (C.BinOp
                            ( C.Add,
                              lo_expr,
                              C.Cast (C.Basic "int32_t", C.Id index_var) ))
                         vm
                     else vm
                   in
                   (vm', pid + 1))
                 (body_vm, 0)
            |> fst
        | _ -> body_vm
      in

      let body_stmts, _body_env =
        lower_graph
          { gen_env with var_map = body_vm; parent_env = Some gen_env }
          body_gr body_gid
      in

      (* Body result = BODY's pre-declared boundary-out variable at port 0 *)
      let body_res = C.Id (var_name body_gid 0 0 `In) in

      let cast_ptr =
        C.Cast (C.Pointer (C.Basic cast_ty, []), C.Member (res_v, "data"))
      in
      let write_stmt =
        C.Expr
          (C.BinOp (C.Assign, C.Index (cast_ptr, C.Id index_var), body_res))
      in

      ( gen_stmts
        @ [
            alloc_stmt;
            lo_bound_stmt;
            C.GCDApply
              ( count_expr,
                "dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0)",
                (index_var, body_stmts @ [ write_stmt ]) );
          ],
        env )

let lower_procedure tm nid node =
  next_dyn_gid := 1_000_000;
  match node with
  | Compound (_, INTERNAL, _, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name s -> Some s | _ -> None) pr
        |> Option.value ~default:(Printf.sprintf "func_%d" nid)
      in
      let is_gpu_func =
        contains_substr (String.uppercase_ascii func_name) "GPU"
      in
      let gid_table = build_gid_table sub_gr in
      let sub_gid = 0 in
      (* root graph of this function is always gid 0 *)
      (* Build port→ty_id from boundary output edges (source=node 0); the
         boundary metadata stores ty_id=0 for all entries so edges are authoritative. *)
      let boundary_port_types =
        ES.fold
          (fun ((sn, sp), _, ty_id) m ->
            if sn = 0 then IntMap.add sp ty_id m else m)
          sub_gr.eset IntMap.empty
      in
      (* Fallback for LET_NON_REC-wrapped functions: no direct sn=0 edges in the
         outer graph.  Search compound children's inner graphs. *)
      let boundary_port_types =
        NM.fold
          (fun _ node m ->
            match node with
            | Compound (_, _, _, _, sg, _) ->
                ES.fold
                  (fun ((sn, sp), _, t) acc ->
                    if sn = 0 && t <> 0 && not (IntMap.mem sp acc) then
                      IntMap.add sp t acc
                    else acc)
                  sg.eset m
            | _ -> m)
          sub_gr.nmap boundary_port_types
      in
      let params =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            let sorted_ins =
              List.sort (fun (_, p1, _) (_, p2, _) -> compare p1 p2) ins
            in
            List.filter_map
              (fun (ty_id, pid, name) ->
                let sname = sanitize name in
                if sname = "" then None
                else
                  let final_ty_id =
                    if ty_id <> 0 then ty_id
                    else try IntMap.find pid boundary_port_types with _ -> 0
                  in
                  let if1_ty =
                    try TM.find final_ty_id tm with _ -> Unknown_ty
                  in
                  (* Fallback: if name looks like an integer parameter, assume int32_t *)
                  let c_ty =
                    if if1_ty = Unknown_ty then
                      if sname = "n" || sname = "i" then C.Basic "int32_t"
                      else if sname = "a" || sname = "b" then
                        C.Basic "sisal_array_t"
                      else C.Basic "int32_t"
                    else c_type_of_if1_ty tm if1_ty
                  in
                  Some (c_ty, sname))
              sorted_ins
        | _ -> []
      in
      let var_map =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.fold_left
              (fun m (_, pid, name) ->
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
          gid_table;
        }
      in
      let body_stmts, env_after = lower_graph env sub_gr sub_gid in
      let body_stmts = [ C.Compound body_stmts ] in

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
          (fun pid ->
            let res_v =
              FullPortMap.find_opt (sub_gid, 0, pid, `In) env_after.var_map
              |> Option.value
                   ~default:(C.Id (var_name ~tag:"func_res" sub_gid 0 pid `In))
            in
            (pid, res_v))
          all_b_outs
      in

      let body_stmts_unwrapped =
        match body_stmts with [ C.Compound stmts ] -> stmts | _ -> body_stmts
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
          body_stmts_unwrapped
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
              body = body_stmts_unwrapped @ [ C.Return (Some e) ];
              extern_c = true;
            },
            None )
      else
        Some
          ( {
              C.return_ty = C.Void;
              name = func_name;
              params;
              body = body_stmts_unwrapped;
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
