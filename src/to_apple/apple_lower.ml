(** apple_lower.ml: The "Apple Lowering" pass for Sisal. This module implements
    the complex logic of translating dataflow IF1 graphs into imperative C-AST
    nodes, optimized for Apple Silicon. *)

open Ir.If1
open Apple_env
open Apple_helpers

module StringMap = Map.Make (String)

(** [c_op_of_node_sym sym] maps a basic IF1 node symbol to a C binary operator.
*)
let c_op_of_node_sym = function
  | ADD -> Some C.Add
  | SUBTRACT -> Some C.Sub
  | TIMES -> Some C.Mul
  | EQUAL -> Some C.Eq
  | NOT_EQUAL -> Some C.Ne
  | GREATER -> Some C.Gt
  | GREATER_EQUAL -> Some C.Ge
  | LESSER -> Some C.Lt
  | LESSER_EQUAL -> Some C.Le
  | _ -> None

(** [rank_of_type tm ty] — STATIC rank of an IF1 type: the count of nested
    Array_dv/Array_ty wrappers.  NOTE: for array_dv VALUES the authoritative
    rank is the runtime dope field (a.rank); this static count only reflects
    type-level nesting, which the flat-dv model keeps at 1 for any rank. *)
let rec rank_of_type tm = function
  | Array_dv t -> 1 + (match TM.find_opt t tm with Some ty -> rank_of_type tm ty | None -> 0)
  | Array_ty t -> 1 + (match TM.find_opt t tm with Some ty -> rank_of_type tm ty | None -> 0)
  | _ -> 0

(** [rank_of_type_id tm tid] — rank_of_type looked up by typemap id. *)
let rank_of_type_id tm tid =
  match TM.find_opt tid tm with
  | Some ty -> rank_of_type tm ty
  | None -> 0

(** [string_of_c_type ty] — compact C spelling of a C-AST type, used for
    SISAL_CAST's template argument (local variant; the full printer lives in
    C_ast_print). *)
let string_of_c_type = function
  | C.Basic s -> s
  | C.Pointer (C.Basic s, _) -> s ^ "*"
  | _ -> "int32_t"

(* A forall RETURNS reduction operator.  Previously stringly-typed (Some "sum" /
   "argmax" / …), which let an unrecognised RETURNS kind silently fall through to
   the gather path.  A closed variant makes the lowering matches exhaustive, so a
   new/unknown operator is a type error rather than a wrong-answer miscompile. *)
type reduce_op =
  | R_sum
  | R_product
  | R_least
  | R_greatest
  | R_argmax
  | R_argmin
  | R_catenate

(* Parse the operator name carried by the REDUCE node's CHARACTER literal.  Fails
   loudly on anything unexpected — an unknown reduction is a bug, not a default. *)
let reduce_op_of_string s =
  match String.lowercase_ascii s with
  | "sum" -> R_sum
  | "product" -> R_product
  | "least" -> R_least
  | "greatest" -> R_greatest
  | "argmax" -> R_argmax
  | "argmin" -> R_argmin
  | "catenate" -> R_catenate
  | other ->
      failwith (Printf.sprintf "forall reduce: unknown operator %S" other)

(* Return Some op when the FORALL's RETURNS subgraph folds to a scalar via REDUCE.
   Used by both infer_types (to suppress the sisal_array_t seed) and lower_forall. *)
let forall_fold_op loop_gr =
  (* A pure fold FORALL has exactly ONE body output (the element to reduce).
     Multi-output FORALLs (e.g. DV_CONFORM with array + boolean outputs) use the
     gather path instead, so return None for them. *)
  let body_out_count =
    match find_subgraph loop_gr "BODY" with
    | None -> 0
    | Some (_, b_gr) ->
        ES.fold
          (fun (_, (dn, _), _) acc -> if dn = 0 then acc + 1 else acc)
          b_gr.eset 0
  in
  if body_out_count <> 1 then None
  else
    match find_subgraph loop_gr "RETURNS" with
    | None -> None
    | Some (_, ret_gr) ->
        NM.fold
          (fun reduce_nid node acc ->
            match node with
            | Simple (_, REDUCE, _, _, _) -> (
                let op =
                  ES.fold
                    (fun ((sn, _), (dn, dp), _) a ->
                      if dn = reduce_nid && dp = 0 then
                        match NM.find_opt sn ret_gr.nmap with
                        | Some (Literal (_, CHARACTER, value, _)) ->
                            Some (reduce_op_of_string value)
                        | _ -> a
                      else a)
                    ret_gr.eset None
                in
                match op with Some _ -> op | None -> acc)
            | _ -> acc)
          ret_gr.nmap None

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
            List.filter_map
              (fun (_, _, name, bp) ->
                if String.length name > plen && String.sub name 0 plen = pfx
                then
                  try
                    Some
                      ( bp,
                        int_of_string
                          (String.sub name plen (String.length name - plen)) )
                  with _ -> None
                else None)
              ins
        | _ -> []
      in
      ES.fold
        (fun ((sn, _), (dn, dp), _) acc ->
          if dn = 0 then
            match NM.find_opt sn ret_gr.nmap with
            | Some (Simple (_, REDUCE, _, _, _)) -> (
                let op =
                  ES.fold
                    (fun ((s, _), (d, p), _) a ->
                      if d = sn && p = 0 then
                        match NM.find_opt s ret_gr.nmap with
                        | Some (Literal (_, CHARACTER, v, _)) ->
                            Some (reduce_op_of_string v)
                        | _ -> a
                      else a)
                    ret_gr.eset None
                in
                let bport =
                  ES.fold
                    (fun ((s, sp), (d, p), _) a ->
                      if d = sn && p = 1 && s = 0 then
                        match List.assoc_opt sp bin_to_body with
                        | Some b -> Some b
                        | None -> a
                      else a)
                    ret_gr.eset None
                in
                match op with
                | Some o ->
                    (dp, o, match bport with Some b -> b | None -> 0) :: acc
                | None -> acc)
            | _ -> acc
          else acc)
        ret_gr.eset []

(** [forall_reduce_filter_of loop_gr out_port] — for a forall RETURNS
    reduction at [out_port], the BODY output port carrying its `when` mask
    (the boolean filter), or None when the reduction is unmasked.  Resolved
    through the __forall_body_<k> boundary-name convention. *)
let forall_reduce_filter_of loop_gr out_port =
  match find_subgraph loop_gr "RETURNS" with
  | None -> None
  | Some (_, ret_gr) ->
      let bin_to_body =
        match NM.find_opt 0 ret_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.filter_map
              (fun (_, sp, name, bp) ->
                if (String.length name >= 14 && String.sub name 0 14 = "__forall_mask_") ||
                   (String.length name >= 15 && String.sub name 0 15 = "__forall_body_")
                then Some (bp, sp)
                else None)
              ins
        | _ -> []
      in
      ES.fold
        (fun ((sn, _), (dn, dp), _) acc ->
          if dn = 0 && dp = out_port then
            match NM.find_opt sn ret_gr.nmap with
            | Some (Simple (_, REDUCE, _, _, _)) -> (
                let fport =
                  ES.fold
                    (fun ((s, sp), (d, p), _) a ->
                      if d = sn && p = 2 && s = 0 then
                        match List.assoc_opt sp bin_to_body with
                        | Some b -> Some b
                        | None -> a
                      else a)
                    ret_gr.eset None
                in
                fport)
            | _ -> acc
          else acc)
        ret_gr.eset None

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
            List.filter_map
              (fun (_, _, name, bp) ->
                if String.length name > plen && String.sub name 0 plen = pfx
                then
                  try
                    Some
                      ( bp,
                        int_of_string
                          (String.sub name plen (String.length name - plen)) )
                  with _ -> None
                else None)
              ins
        | _ -> []
      in
      ES.fold
        (fun ((sn, _), (dn, dp), _) acc ->
          if dn = 0 then
            match NM.find_opt sn ret_gr.nmap with
            | Some (Simple (_, (DV_GATHER | AGATHER | DV_SCATTER_AT), _, _, _))
              ->
                let bport =
                  ES.fold
                    (fun ((s, sp), (d, p), _) a ->
                      if d = sn && p = 1 && s = 0 then
                        match List.assoc_opt sp bin_to_body with
                        | Some b -> Some b
                        | None -> a
                      else a)
                    ret_gr.eset None
                in
                (dp, match bport with Some b -> b | None -> dp) :: acc
            | _ -> acc
          else acc)
        ret_gr.eset []

(* Companion to forall_reduce_ports / forall_gather_ports: RETURNS outputs fed by a
   FINALVALUE node — `returns value of X` with NO reduction operator, which keeps the
   LAST iteration's value (not a gather, not a fold).  The value is FINALVALUE's
   port-0 input.  Returns (returns_out_port, body_out_port) per such output. *)
let forall_finalvalue_ports loop_gr =
  match find_subgraph loop_gr "RETURNS" with
  | None -> []
  | Some (_, ret_gr) ->
      let pfx = "__forall_body_" in
      let plen = String.length pfx in
      let bin_to_body =
        match NM.find_opt 0 ret_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.filter_map
              (fun (_, _, name, bp) ->
                if String.length name > plen && String.sub name 0 plen = pfx
                then
                  try
                    Some
                      ( bp,
                        int_of_string
                          (String.sub name plen (String.length name - plen)) )
                  with _ -> None
                else None)
              ins
        | _ -> []
      in
      ES.fold
        (fun ((sn, _), (dn, dp), _) acc ->
          if dn = 0 then
            match NM.find_opt sn ret_gr.nmap with
            | Some (Simple (_, FINALVALUE, _, _, _)) ->
                let bport =
                  ES.fold
                    (fun ((s, sp), (d, p), _) a ->
                      if d = sn && p = 0 && s = 0 then
                        match List.assoc_opt sp bin_to_body with
                        | Some b -> Some b
                        | None -> a
                      else a)
                    ret_gr.eset None
                in
                (dp, match bport with Some b -> b | None -> dp) :: acc
            | _ -> acc
          else acc)
        ret_gr.eset []

(* For-initial RETURNS gather.  Unlike forall_gather_ports (which keys boundary
   inputs by the __forall_body_ prefix), a for-initial RETURNS names its boundary
   inputs __ret_N (the multi-return convention).  Returns, per DV_GATHER output,
   (returns_out_port, returns_boundary_in_port): the boundary-in port carries the
   gathered per-iteration value, which the caller resolves to a BODY output (and
   thence the body-capture var) via the loop-level edge set. *)
let for_initial_gather_ports ret_gr =
  ES.fold
    (fun ((sn, _), (dn, dp), _) acc ->
      if dn = 0 then
        match NM.find_opt sn ret_gr.nmap with
        | Some (Simple (_, (DV_GATHER | AGATHER | DV_SCATTER_AT), _, _, _)) -> (
            let bin =
              ES.fold
                (fun ((s, sp), (d, p), _) a ->
                  if d = sn && p = 1 && s = 0 then Some sp else a)
                ret_gr.eset None
            in
            match bin with Some b -> (dp, b) :: acc | None -> acc)
        | _ -> acc
      else acc)
    ret_gr.eset []

(** [infer_types env gr gid] populates the type_table for the current graph
    hierarchy. *)
let infer_types env gr gid =
  let _, tm, _ = gr.typemap in
  let table = Hashtbl.create 256 in
  FullPortMap.iter (fun k v -> Hashtbl.replace table k v) env.type_table;

  let set_ty g n p d ty =
    let key = (g, n, p, d) in
    match Hashtbl.find_opt table key with
    | Some existing when existing = C.Basic "sisal_array_t" -> ()
    | _ -> Hashtbl.replace table key ty
  in

  (* Like set_ty but returns true when the value actually changed — used to drive pass2 fixpoint. *)
  let set_ty_c g n p d ty =
    let key = (g, n, p, d) in
    match Hashtbl.find_opt table key with
    | Some ex when ex = C.Basic "sisal_array_t" -> false
    | Some ex when ex = ty -> false
    | _ ->
        Hashtbl.replace table key ty;
        true
  in

  let get_ty g n p d =
    match Hashtbl.find_opt table (g, n, p, d) with
    | Some ty -> ty
    | None -> C.Basic "float"
  in

  let rec pass1 g cur_gid =
    let cs, _ps = g.symtab in
    SM.iter
      (fun _ v ->
        set_ty cur_gid v.val_def v.def_port `Out
          (c_type_of_if1_tyid tm v.val_ty))
      cs;
    NM.iter
      (fun nid node ->
        match node with
        | Boundary _ -> ()
        | Literal (_, code, _, _) ->
            let ty =
              match code with
              | REAL | DOUBLE -> C.Basic "double"
              | BOOLEAN -> C.Basic "bool"
              | _ -> C.Basic "int32_t"
            in
            set_ty cur_gid nid 0 `Out ty
        | Simple (_, sym, _, outs, _) ->
            let is_int =
              List.mem sym
                [
                  RANGEGEN;
                  ALIML;
                  ALIMH;
                  ASIZE;
                  DV_DIMENSION;
                  DV_NUM_RANK;
                  DV_OFFSET_AT;
                  DV_SIZE;
                  DV_LIML;
                  DV_LIMH;
                ]
            in
            let is_arr =
              List.mem sym
                [
                  DV_CREATE;
                  DV_RESHAPE;
                  DV_SLICE;
                  DV_PERMUTE;
                  DV_ROTATE;
                  DV_COMPRESS;
                  DV_OUTERPRODUCT;
                  DV_SORT;
                  DV_REVERSE;
                  DV_RESHAPE_BY_SHAPE;
                  DV_GATHER;
                  DV_SCATTER_AT;
                  AGATHER;
                  ASCATTER;
                  ABUILD;
                  AFILL;
                  ACREATE;
                  AREPLACE;
                  AADDH;
                  DVAADDH;
                  ACATENATE;
                  DVAFILL;
                  DVAADDL;
                  DVABUILD;
                  DVAADJUST;
                  DV_RANK_REDUCE;
                  DV_RANK_REPLACE;
                  DV_REPLACE;
                  DV_SETL;
                  ASETL;
                  GET_DOPE_VEC;
                ]
            in
            let ty =
              if is_int then C.Basic "int32_t"
              else if is_arr then C.Basic "sisal_array_t"
              else C.Basic "float"
            in
            Array.iteri (fun i _ -> set_ty cur_gid nid i `Out ty) outs;
            (* RBUILD/RELEMENTS: type outputs from the OUT EDGE's IF1 type id
               -- the only way a record output gets its `struct struct_rec_N`
               C type (the default float would make assign_with_cast emit
               SISAL_CAST(float, struct)). *)
            (if sym = RBUILD || sym = RELEMENTS || sym = RREPLACE then
               let _, gtm, _ = g.typemap in
               ES.iter
                 (fun ((sn, sp), _, tyid) ->
                   if sn = nid && tyid <> 0 then
                     set_ty cur_gid nid sp `Out (c_type_of_if1_tyid gtm tyid))
                 g.eset);
            (* AFILL takes (lo, hi, val) -- port 0 is an int bound, NOT an array -- so it is
             array-producing (is_arr) yet must NOT have port 0 coerced to sisal_array_t. *)
            if
              (is_arr && sym <> DVAFILL && sym <> DVAADJUST)
              || List.mem sym
                   [
                     ALIML;
                     ALIMH;
                     ASIZE;
                     DV_SCATTER;
                     AELEMENT;
                     DV_ELEMENT;
                     DV_LOAD_LINEAR;
                     DV_DIMENSION;
                     DV_COMPRESS;
                     DV_SORT;
                     DV_REVERSE;
                     DV_ROTATE;
                     DV_SLICE;
                     DV_PERMUTE;
                     REDUCE_ALL;
                     DV_SIZE;
                     DV_LIML;
                     DV_LIMH;
                     DV_REPLACE;
                     DV_SETL;
                   ]
            then set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t");
            if sym = DV_RANK_REDUCE || sym = DV_PERMUTE then begin
              for i = 1 to 40 do
                set_ty cur_gid nid i `In (C.Basic "int32_t")
              done
            end
        | Compound (_, sym, _, pr, sub, _) ->
            let sub_gid =
              try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1
            in
            let is_forall = get_compound_type pr = If1_forall in
            let fold_op = if is_forall then forall_fold_op sub else None in
            let is_fold = fold_op <> None in
            (* A multi-output forall may have REDUCTION output ports (value of sum, …).
             Don't seed port 0 as sisal_array_t when it's a reduction -- let pass2
             infer its scalar type from the REDUCE output edge (as it already does for
             the other reduction ports). *)
            let rports = if is_forall then forall_reduce_ports sub else [] in
            let port0_is_reduce =
              List.exists (fun (dp, _, _) -> dp = 0) rports
            in
            (* FINALVALUE (`value of X`, no operator) keeps the body value's own type
             (array OR scalar) — don't force sisal_array_t; let pass2 infer it. *)
            let fports =
              if is_forall then forall_finalvalue_ports sub else []
            in
            let port0_is_final = List.exists (fun (dp, _) -> dp = 0) fports in
            if
              (is_forall || sym = STREAM || sym = MAT)
              && (not is_fold) && (not port0_is_reduce) && not port0_is_final
            then set_ty cur_gid nid 0 `Out (C.Basic "sisal_array_t");
            (match fold_op with
            | Some (R_argmax | R_argmin) ->
                set_ty cur_gid nid 0 `Out (C.Basic "int32_t")
            | _ -> ());
            pass1 sub sub_gid
        | _ -> ())
      g.nmap
  in

  let rec pass2 g cur_gid =
    let tm2 = get_typemap_tm g in
    let changed_edges =
      ES.fold
        (fun ((sn, sp), (dn, dp), ty_id) ch ->
          let sty = get_ty cur_gid sn sp `Out in
          let dty = get_ty cur_gid dn dp `In in
          (* Seed concrete types from edge type tags (e.g. INTEGRAL on DV_ELEMENT output edges).
         Only seed the destination when the source agrees or is still unknown — prevents
         body-expression edge tags (e.g. DOUBLE on an argmax output) from overriding a
         source that pass0/pass1 already typed as int32_t. *)
          let c0 =
            let ety = c_type_of_if1_tyid tm2 ty_id in
            if ety <> C.Basic "float" then
              let c1 =
                if sty = C.Basic "float" then
                  set_ty_c cur_gid sn sp `Out ety
                else false
              in
              let c2 =
                if
                  dty = C.Basic "float"
                  && (sty = C.Basic "float" || sty = ety)
                then set_ty_c cur_gid dn dp `In ety
                else false
              in
              c1 || c2
            else false
          in
          let sty = get_ty cur_gid sn sp `Out in
          let dty = get_ty cur_gid dn dp `In in
          let c1 =
            if sty <> C.Basic "float" && dty = C.Basic "float" then
              set_ty_c cur_gid dn dp `In sty
            else false
          in
          let c2 =
            if dty <> C.Basic "float" && sty = C.Basic "float" then
              set_ty_c cur_gid sn sp `Out dty
            else false
          in
          ch || c0 || c1 || c2)
        g.eset false
    in
    let changed_nodes =
      NM.fold
        (fun nid node ch ->
          match node with
          | Simple (_, sym, _, _, _) ->
              let c1 =
                if
                  List.mem sym
                    [
                      ALIML;
                      ALIMH;
                      ASIZE;
                      AELEMENT;
                      DV_ELEMENT;
                      DV_RANK_REDUCE;
                      DV_RANK_REPLACE;
                      DV_LOAD_LINEAR;
                      DV_DIMENSION;
                      DV_COMPRESS;
                      DV_SORT;
                      DV_REVERSE;
                      DV_ROTATE;
                      DV_SLICE;
                      DV_PERMUTE;
                      REDUCE_ALL;
                      AREPLACE;
                      DV_SIZE;
                      DV_LIML;
                      DV_LIMH;
                      DV_REPLACE;
                      DV_SETL;
                    ]
                then
                  let in0 = get_ty cur_gid nid 0 `In in
                  if in0 = C.Basic "float" then
                    set_ty_c cur_gid nid 0 `In (C.Basic "sisal_array_t")
                  else false
                else false
              in
              let c2 =
                if
                  sym = AELEMENT || sym = DV_ELEMENT || sym = DV_RANK_REDUCE
                  || sym = DV_RANK_REPLACE || sym = DV_LOAD_LINEAR
                  || sym = DV_OFFSET_AT || sym = DV_DIMENSION || sym = AREPLACE
                  || sym = DV_REPLACE
                then
                  let in1 = get_ty cur_gid nid 1 `In in
                  if in1 = C.Basic "float" then
                    set_ty_c cur_gid nid 1 `In (C.Basic "int32_t")
                  else false
                else false
              in
              ch || c1 || c2
          | Compound (_, _, _, _, sub, _) ->
              let sub_gid =
                try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1
              in
              let b_ins =
                match NM.find_opt 0 sub.nmap with
                | Some (Boundary (ins, _, _, _)) -> List.length ins
                | _ -> 0
              in
              (* Use eset to find actual boundary outputs — boundary outs metadata is often stale.
             Exclude error edges so error-flow ports aren't treated as return values. *)
              let sub_return_ports =
                ES.fold
                  (fun (_, (dn, dp), ty) acc ->
                    if dn = 0 && not (is_error_port ty sub) then
                      IntSet.add dp acc
                    else acc)
                  sub.eset IntSet.empty
              in
              let c1 =
                List.fold_left
                  (fun ch i ->
                    let p_ty = get_ty cur_gid nid i `In in
                    let c_ty = get_ty sub_gid 0 i `Out in
                    let ca =
                      if p_ty <> C.Basic "float" && c_ty = C.Basic "float" then
                        set_ty_c sub_gid 0 i `Out p_ty
                      else false
                    in
                    let cb =
                      if c_ty <> C.Basic "float" && p_ty = C.Basic "float" then
                        set_ty_c cur_gid nid i `In c_ty
                      else false
                    in
                    ch || ca || cb)
                  false (List.init b_ins Fun.id)
              in
              let c2 =
                IntSet.fold
                  (fun i ch ->
                    let c_ty = get_ty sub_gid 0 i `In in
                    let p_ty = get_ty cur_gid nid i `Out in
                    let ca =
                      if c_ty <> C.Basic "float" && p_ty = C.Basic "float" then
                        set_ty_c cur_gid nid i `Out c_ty
                      else false
                    in
                    let cb =
                      if p_ty <> C.Basic "float" && c_ty = C.Basic "float" then
                        set_ty_c sub_gid 0 i `In p_ty
                      else false
                    in
                    ch || ca || cb)
                  sub_return_ports false
              in
              pass2 sub sub_gid;
              ch || c1 || c2
          | _ -> ch)
        g.nmap false
    in
    if changed_edges || changed_nodes then pass2 g cur_gid
  in

  let rec pass0 g cur_gid =
    NM.iter
      (fun nid node ->
        match node with
        | Simple (_, sym, _, outs, _) ->
            let is_arr =
              List.mem sym
                [
                  DV_CREATE;
                  DV_RESHAPE;
                  DV_SLICE;
                  DV_PERMUTE;
                  DV_ROTATE;
                  DV_COMPRESS;
                  DV_OUTERPRODUCT;
                  DV_SORT;
                  DV_REVERSE;
                  DV_RESHAPE_BY_SHAPE;
                  DV_GATHER;
                  DV_SCATTER_AT;
                  AGATHER;
                  ASCATTER;
                  ABUILD;
                  AFILL;
                  ACREATE;
                  AREPLACE;
                  AADDH;
                  DVAADDH;
                  ACATENATE;
                  DVAFILL;
                  DVAADDL;
                  DVABUILD;
                  DVAADJUST;
                  DV_RANK_REDUCE;
                  DV_RANK_REPLACE;
                  DV_REPLACE;
                  DV_SETL;
                  ASETL;
                ]
            in
            if is_arr then (
              Array.iteri
                (fun i _ -> set_ty cur_gid nid i `Out (C.Basic "sisal_array_t"))
                outs;
              (* AFILL's port 0 is an int bound (lo), not an array -- don't coerce it *)
              if sym <> DVAFILL && sym <> DVAADJUST then
                set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t"));
            if
              List.mem sym
                [
                  ALIML;
                  ALIMH;
                  ASIZE;
                  DV_SCATTER;
                  AELEMENT;
                  DV_ELEMENT;
                  DV_LOAD_LINEAR;
                  DV_DIMENSION;
                  DV_COMPRESS;
                  DV_SORT;
                  DV_REVERSE;
                  DV_ROTATE;
                  DV_SLICE;
                  DV_PERMUTE;
                  REDUCE_ALL;
                  DV_SIZE;
                  DV_LIML;
                  DV_LIMH;
                  DV_REPLACE;
                  DV_SETL;
                ]
            then set_ty cur_gid nid 0 `In (C.Basic "sisal_array_t")
        | Compound (_, sym, _, pr, sub, _) ->
            let sub_gid =
              try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1
            in
            let is_forall = get_compound_type pr = If1_forall in
            let fold_op = if is_forall then forall_fold_op sub else None in
            let is_fold = fold_op <> None in
            (* A multi-output forall may have REDUCTION output ports (value of sum, …).
             Don't seed port 0 as sisal_array_t when it's a reduction -- let pass2
             infer its scalar type from the REDUCE output edge (as it already does for
             the other reduction ports). *)
            let rports = if is_forall then forall_reduce_ports sub else [] in
            let port0_is_reduce =
              List.exists (fun (dp, _, _) -> dp = 0) rports
            in
            (* FINALVALUE (`value of X`, no operator) keeps the body value's own type
             (array OR scalar) — don't force sisal_array_t; let pass2 infer it. *)
            let fports =
              if is_forall then forall_finalvalue_ports sub else []
            in
            let port0_is_final = List.exists (fun (dp, _) -> dp = 0) fports in
            if
              (is_forall || sym = STREAM || sym = MAT)
              && (not is_fold) && (not port0_is_reduce) && not port0_is_final
            then set_ty cur_gid nid 0 `Out (C.Basic "sisal_array_t");
            (match fold_op with
            | Some (R_argmax | R_argmin) ->
                set_ty cur_gid nid 0 `Out (C.Basic "int32_t")
            | _ -> ());
            pass0 sub sub_gid
        | _ -> ())
      g.nmap
  in

  pass0 gr gid;
  pass1 gr gid;
  pass2 gr gid;
  {
    env with
    type_table =
      Hashtbl.fold (fun k v m -> FullPortMap.add k v m) table FullPortMap.empty;
  }

(** [get_final_ty env gid nid pid dir] — the C type infer_types settled on
    for a port, from env.type_table.  Defaults to float when the port was
    never typed (the known inference gap: untyped double intermediates ride
    float slots). *)
let get_final_ty env gid nid pid dir =
  match FullPortMap.find_opt (gid, nid, pid, dir) env.type_table with
  | Some ty -> ty
  | None -> C.Basic "float"

(** [is_proc_expr env g n] checks if a node represents a global procedure. *)
let is_proc_expr env g n =
  if g = 0 then
    match IntMap.find_opt n env.proc_map with Some _ -> true | None -> false
  else false

(** [scan_fanout gr gid env] populates the fanout_map for the current graph. *)
let scan_fanout gr gid env =
  let fanout_map =
    ES.fold
      (fun ((sn, sp), _, _) fmap ->
        let key = (gid, sn, sp) in
        PortFanout.add key
          (1 + match PortFanout.find_opt key fmap with Some c -> c | None -> 0)
          fmap)
      gr.eset env.fanout_map
  in
  { env with fanout_map }

(** [assign_with_cast env gid nid pid dir src_expr] emits an assignment with an
    optional declaration if the variable is seen for the first time. *)
let assign_with_cast env gid nid pid dir src_expr =
  let is_proc =
    match src_expr with
    | C.Id n -> String.length n >= 5 && String.sub n 0 5 = "func_"
    | _ -> false
  in
  if is_proc || is_proc_expr env gid nid then
    ( [
        C.Comment
          ("Skipped function-as-value assignment: "
          ^ match src_expr with C.Id n -> n | _ -> "unknown");
      ],
      env )
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
    let cast_expr =
      C.Call ("SISAL_CAST", [ C.Id (string_of_c_type dst_ty); src_expr ])
    in
    if StringSet.mem name env.seen_decls then
      ([ C.Expr (C.BinOp (C.Assign, v_res, cast_expr)) ], env)
    else
      let init_val = default_init_for dst_ty in
      let decl = C.Decl (dst_ty, name, init_val) in
      let assign = C.Expr (C.BinOp (C.Assign, v_res, cast_expr)) in
      let env' =
        {
          env with
          seen_decls = StringSet.add name env.seen_decls;
          var_map = FullPortMap.add (gid, nid, pid, dir) v_res env.var_map;
        }
      in
      ([ decl; assign ], env')

(** [declare_outputs env gr gid nid node] selectively pre-declares outputs of a
    compound node in its parent scope. *)
let declare_outputs env gr gid nid node =
  let out_pids, out_dir =
    match node with
    | Simple (_, _, _, outs, _) ->
        (Array.mapi (fun i _ -> i) outs |> Array.to_list, `Out)
    | Compound _ ->
        (* Derive from parent eset: all edges where this compound node is the source.
           This matches exactly the set lower_node's res_prop will iterate, ensuring
           every assigned port is pre-declared in the outer scope. *)
        let ports =
          ES.fold
            (fun ((sn, sp), _, _) acc ->
              if sn = nid then IntSet.add sp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        (ports, `Out)
    | _ -> ([], `Out)
  in
  List.fold_left
    (fun (acc_stmts, e) pid ->
      let name = get_c_name e.proc_map e.gid_name_map gid nid pid out_dir gr in
      if StringSet.mem name e.seen_decls then (acc_stmts, e)
      else
        let ty = get_final_ty e gid nid pid out_dir in
        let init_val = default_init_for ty in
        ( acc_stmts @ [ C.Decl (ty, name, init_val) ],
          {
            e with
            seen_decls = StringSet.add name e.seen_decls;
            var_map =
              FullPortMap.add (gid, nid, pid, out_dir) (C.Id name) e.var_map;
          } ))
    ([], env) out_pids

(** [pre_declare_graph_locals env gr gid] declares all symbols in the graph's
    LOCAL symtab and its outputs (Boundary inputs). *)
let pre_declare_graph_locals env gr gid =
  (* 1. Declare all named symbols from the LOCAL-SYM table, one C variable per name *)
  let cs, _ps = gr.symtab in
  let stmts1, env1 =
    SM.fold
      (fun _ v (acc_stmts, e) ->
        if is_proc_expr e gid v.val_def then (acc_stmts, e)
        else
          let name =
            Printf.sprintf "v_%s_n__%d_%s"
              (scope_of e.gid_name_map gid)
              v.val_def (sanitize v.val_name)
          in
          if StringSet.mem name e.seen_decls then (acc_stmts, e)
          else
            let ty = get_final_ty e gid v.val_def v.def_port `Out in
            let init_val = default_init_for ty in
            ( acc_stmts @ [ C.Decl (ty, name, init_val) ],
              {
                e with
                seen_decls = StringSet.add name e.seen_decls;
                var_map =
                  FullPortMap.add
                    (gid, v.val_def, v.def_port, `Out)
                    (C.Id name) e.var_map;
              } ))
      cs ([], env)
  in

  (* 2. Declare boundary in-ports (node 0 out-ports) by scanning the edge set.
        Boundary.ins adjacency list is unreliable (stale/debug only); edges are authoritative. *)
  let boundary_in_ports =
    ES.fold
      (fun ((sn, sp), _, _) acc -> if sn = 0 then IntSet.add sp acc else acc)
      gr.eset IntSet.empty
  in
  let stmts2, env2 =
    IntSet.fold
      (fun i (acc_stmts, e) ->
        let name = get_c_name e.proc_map e.gid_name_map gid 0 i `Out gr in
        if StringSet.mem name e.seen_decls then (acc_stmts, e)
        else
          let ty = get_final_ty e gid 0 i `Out in
          let init_val =
            match FullPortMap.find_opt (gid, 0, i, `Out) e.proc_param_map with
            | Some arg_expr -> Some arg_expr
            | None -> default_init_for ty
          in
          ( acc_stmts @ [ C.Decl (ty, name, init_val) ],
            {
              e with
              seen_decls = StringSet.add name e.seen_decls;
              var_map = FullPortMap.add (gid, 0, i, `Out) (C.Id name) e.var_map;
            } ))
      boundary_in_ports ([], env1)
  in
  (stmts1 @ stmts2, env2)

let init_boundary_ports env parent_gr compound_nid gr gid =
  if gid = 0 then ([], env)
  else
    (* Use parent_gr.eset edges into compound_nid — authoritative, never stale.
       Boundary.ins adjacency list is unreliable (stale/debug only). *)
    let pgid =
      match env.parent_env with
      | Some pe -> pe.curr_gid
      | None -> (
          match IntMap.find_opt gid env.parent_map with
          | Some (p, _) -> p
          | _ -> 0)
    in
    let edges_to_compound =
      ES.fold
        (fun ((sn, sp), (dn, dp), _) acc ->
          if dn = compound_nid then IntMap.add dp (sn, sp) acc else acc)
        parent_gr.eset IntMap.empty
    in
    IntMap.fold
      (fun dp (psrcN, psrcP) (acc_stmts, e) ->
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
                  | Some pe -> (
                      match
                        FullPortMap.find_opt
                          (pe.curr_gid, psrcN, psrcP, `Out)
                          e.var_map
                      with
                      | Some v -> Some v
                      | None -> search pe)
                in
                search e
        in
        let stmts, e' =
          match src_opt with
          | None -> ([], e)
          | Some src_expr -> assign_with_cast e gid 0 dp `Out src_expr
        in
        (acc_stmts @ stmts, e'))
      edges_to_compound ([], env)

(** [alloc_array_call rank tid count elem_cty] -- the allocation call for an
    array whose ELEMENT C type is [elem_cty].  Records pass sizeof(...)
    explicitly (sisal_array_alloc_sized): type_id is an IF1 typemap id the
    runtime cannot size beyond the preloaded scalars, and the descriptor's
    elem_bytes must be authoritative. *)
let alloc_array_call rank_e tid_e count_e elem_cty =
  if is_struct_cty elem_cty || elem_cty = C.Basic "sisal_array_t" then
    C.Call
      ( "sisal_array_alloc_sized",
        [
          rank_e;
          tid_e;
          count_e;
          C.Call ("sizeof", [ C.Id (Ir.C_ast_print.string_of_c_type elem_cty) ]);
        ] )
  else C.Call ("sisal_array_alloc_empty", [ rank_e; tid_e; count_e ])

(** [lower_graph env parent_gr compound_nid gr gid] translates an IF1 graph into
    a list of C statements. *)
let rec lower_graph env parent_gr compound_nid gr gid =
  let env = { env with curr_gid = gid; curr_gr = gr } in
  let env = scan_fanout gr gid env in
  let pre_decl_stmts, env = pre_declare_graph_locals env gr gid in
  let b_in_stmts, env =
    if env.parent_env = None || IntMap.mem gid env.proc_map then ([], env)
    else init_boundary_ports env parent_gr compound_nid gr gid
  in

  let sorted_nodes = topo_sort gr in
  (* The walk, as an explicit recursion.  NOTE on terms: topo_sort already
     yields each node exactly once, so no traversal-correctness "visited" set
     is needed.  [covered] is a COVERING mark (instruction-selection sense:
     tree tiling / maximal munch): nodes whose work was emitted as part of a
     larger unit rooted at an earlier node, with their output ports already
     bound there -- the walk drops them instead of translating them
     independently.  Nothing populates it yet; the catenate-spine fold and
     the dv_dimension+RELEMENTS fusion will. *)
  let rec walk_nodes covered acc_stmts e = function
    | [] -> (acc_stmts, e)
    | nid :: rest when IntSet.mem nid covered ->
        walk_nodes covered acc_stmts e rest
    | 0 :: rest -> walk_nodes covered acc_stmts e rest (* boundary *)
    | nid :: rest -> (
        match NM.find_opt nid gr.nmap with
        | Some (Literal (_, code, value, _)) ->
            let lit =
              match code with
              | REAL | DOUBLE -> C.LitFloat (float_of_string value)
              | BOOLEAN -> C.Id (String.lowercase_ascii value)
              | _ -> (
                  try C.LitInt (int_of_string value) with _ -> C.LitInt 0)
            in
            let stmts, e' = assign_with_cast e gid nid 0 `Out lit in
            walk_nodes covered (acc_stmts @ stmts) e' rest
        | Some node ->
            let node_stmts, e' = lower_node e gr nid node in
            walk_nodes covered (acc_stmts @ node_stmts) e' rest
        | None -> walk_nodes covered acc_stmts e rest)
  in
  let res_stmts, final_env =
    walk_nodes IntSet.empty b_in_stmts env sorted_nodes
  in
  (pre_decl_stmts @ res_stmts, final_env)

(** [lower_node env gr nid node] — lower ONE node.  Compounds dispatch by
    role: forall / if-select / for-initial (LoopA/B) / tagcase get dedicated
    lowerings; other compounds recurse generically via lower_graph.  Simple
    nodes go to lower_simple; Literals emit nothing (resolved at use by
    get_expr). *)
and lower_node env gr nid node =
  let gid = env.curr_gid in
  match node with
  | Compound (cid, sy, _ty, pr, loop_gr, _) ->
      let sub_gid = try GidMap.find (gid, nid) env.gid_table with _ -> -1 in
      let c_of = get_compound_type pr in
      if c_of = If1_forall then lower_forall env gr gid nid loop_gr sub_gid pr
      else if c_of = If1_predicate || c_of = If1_if then
        lower_if_graph env gr nid loop_gr sub_gid
      else if c_of = If1_tagcase then
        lower_tagcase env gr nid loop_gr sub_gid
      else if c_of = If1_loop_initial then
        lower_for_initial env gr gid nid loop_gr sub_gid pr
      else begin
        let decl_stmts, env = declare_outputs env gr gid nid node in
        let env_child =
          {
            env with
            parent_env = Some env;
            compound_nid_in_parent = nid;
            parent_map = IntMap.add sub_gid (gid, nid) env.parent_map;
          }
        in
        let body, env_after = lower_graph env_child gr nid loop_gr sub_gid in
        let out_pids =
          ES.fold
            (fun ((sn, sp), _, _) acc ->
              if sn = nid then IntSet.add sp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let res_prop, final_env =
          List.fold_left
            (fun (acc, e) dp ->
              let src_opt =
                match
                  FullPortMap.find_opt (sub_gid, 0, dp, `In) env_after.var_map
                with
                | Some _ as found -> found
                | None -> (
                    (* boundary In ports aren't populated in var_map by lower_graph;
                   trace via sub-graph eset to find the producing node *)
                    match
                      ES.fold
                        (fun (src, dst, _) a ->
                          if dst = (0, dp) then Some src else a)
                        loop_gr.eset None
                    with
                    | Some (sn, sp) ->
                        FullPortMap.find_opt (sub_gid, sn, sp, `Out)
                          env_after.var_map
                    | None -> None)
              in
              match src_opt with
              | Some src_expr ->
                  let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
                  (acc @ stmts, e')
              | None -> (acc, e))
            ( [],
              {
                env_after with
                curr_gid = gid;
                curr_gr = gr;
                seen_decls = env_after.seen_decls;
              } )
            out_pids
        in
        (decl_stmts @ [ C.Compound (body @ res_prop) ], final_env)
      end
  | Simple (_, sym, pin, pout, pr) -> lower_simple env gr nid sym pin pout pr
  | Literal _ -> ([], env)
  | _ ->
      failwith
        (Printf.sprintf "Unsupported IF1 node type at gid=%d nid=%d" gid nid)

(** [lower_simple env gr nid sym pin pout pr] — one Simple node to C.
    Operands resolve through edges + var_map (get_in_expr wraps them in
    SISAL_CAST to the inferred in-type); the rhs expression is chosen by the
    opcode match; assign_with_cast binds it to the node's output variable.
    Placeholder contracts live here too: DV_GATHER/DV_MAKE_DOPE/DV_SCATTER_AT
    forward e1 (realized structurally by the loop lowerings), and RELEMENTS
    on a collapsed dope triplet passes through.  [pin]/[pout] are the port
    NAME arrays -- pseudo-ports carry record field / union tag names. *)
and lower_simple env gr nid sym pin pout pr =
  let gid = env.curr_gid in
  let get_in_expr p =
    let producers =
      ES.fold
        (fun (src, dst, _) acc -> if dst = (nid, p) then Some src else acc)
        gr.eset None
    in
    match producers with
    | Some (sn, sp) ->
        let ty = get_final_ty env gid nid p `In in
        C.Call
          ( "SISAL_CAST",
            [ C.Id (string_of_c_type ty); get_expr env gid sn sp `Out ] )
    | None -> C.LitInt 0
  in
  let e1 = get_in_expr 0 in
  let e2 = get_in_expr 1 in
  let t_res = get_final_ty env gid nid 0 `Out in
  let rhs =
    match sym with
    | ADD ->
        if t_res = C.Basic "sisal_array_t" then
          C.Call ("sisal_array_add", [ e1; e2 ])
        else C.BinOp (C.Add, e1, e2)
    | SUBTRACT ->
        if t_res = C.Basic "sisal_array_t" then
          C.Call ("sisal_array_sub", [ e1; e2 ])
        else C.BinOp (C.Sub, e1, e2)
    | TIMES ->
        if t_res = C.Basic "sisal_array_t" then
          C.Call ("sisal_array_mul", [ e1; e2 ])
        else C.BinOp (C.Mul, e1, e2)
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
    | AELEMENT ->
        let in_ty = get_final_ty env gid nid 0 `In in
        if in_ty <> C.Basic "sisal_array_t" then
          failwith
            (Printf.sprintf
               "Standard AELEMENT is not supported under the dope vector \
                backend; please use array_dv instead at gid=%d nid=%d"
               gid nid)
        else
          let elem_ty = get_final_ty env gid nid 0 `Out in
          let idx =
            C.BinOp
              (C.Sub, e2, C.Index (C.Member (e1, "lower_bound"), C.LitInt 0))
          in
          let arr_tyid =
            match
              ES.fold
                (fun ((sn, sp), (dn, dp), ty) acc ->
                  if dn = nid && dp = 0 && ty <> 0 then Some ty else acc)
                gr.eset None
            with
            | Some ty -> ty
            | None -> 0
          in
          let rk = rank_of_type_id env.tm arr_tyid in
          if rk > 1 && elem_ty = C.Basic "sisal_array_t" then
            C.Call ("sisal_array_get_row", [ e1; idx ])
          else
            let cast_ptr =
              C.Cast (C.Pointer (elem_ty, []), C.Member (e1, "data"))
            in
            C.Index (cast_ptr, idx)
    | DV_ELEMENT | DV_LOAD_LINEAR ->
        let elem_ty = get_final_ty env gid nid 0 `Out in
        let idx =
          if sym = DV_LOAD_LINEAR then e2
          else
            C.BinOp
              (C.Sub, e2, C.Index (C.Member (e1, "lower_bound"), C.LitInt 0))
        in
        let arr_tyid =
          match
            ES.fold
              (fun ((sn, sp), (dn, dp), ty) acc ->
                if dn = nid && dp = 0 && ty <> 0 then Some ty else acc)
              gr.eset None
          with
          | Some ty -> ty
          | None -> 0
        in
        if sym = DV_ELEMENT && rank_of_type_id env.tm arr_tyid > 1 && elem_ty = C.Basic "sisal_array_t" then
          C.Call ("sisal_array_get_row", [ e1; idx ])
        else
          let cast_ptr =
            C.Cast (C.Pointer (elem_ty, []), C.Member (e1, "data"))
          in
          C.Index (cast_ptr, idx)
    | RANGEGEN -> C.BinOp (C.Add, C.BinOp (C.Sub, e2, e1), C.LitInt 1)
    | ASIZE ->
        let in_ty = get_final_ty env gid nid 0 `In in
        if in_ty <> C.Basic "sisal_array_t" then
          failwith
            (Printf.sprintf
               "Standard ASIZE is not supported under the dope vector backend; \
                please use array_dv instead at gid=%d nid=%d"
               gid nid)
        else
          C.Cast
            ( C.Basic "int32_t",
              C.Cond
                ( C.BinOp
                    ( C.Gt,
                      C.Index (C.Member (e1, "dims"), C.LitInt 0),
                      C.LitInt 0 ),
                  C.Index (C.Member (e1, "dims"), C.LitInt 0),
                  C.Cast (C.Basic "int64_t", C.Member (e1, "size")) ) )
    | DV_SIZE | DV_SCATTER ->
        C.Cast
          ( C.Basic "int32_t",
            C.Cond
              ( C.BinOp
                  (C.Gt, C.Index (C.Member (e1, "dims"), C.LitInt 0), C.LitInt 0),
                C.Index (C.Member (e1, "dims"), C.LitInt 0),
                C.Cast (C.Basic "int64_t", C.Member (e1, "size")) ) )
    | DV_FLAT_SIZE -> C.Cast (C.Basic "int32_t", C.Member (e1, "size"))
    | ALIML ->
        let in_ty = get_final_ty env gid nid 0 `In in
        if in_ty <> C.Basic "sisal_array_t" then
          failwith
            (Printf.sprintf
               "Standard ALIML is not supported under the dope vector backend; \
                please use array_dv instead at gid=%d nid=%d"
               gid nid)
        else
          C.Cast
            ( C.Basic "int32_t",
              C.Index (C.Member (e1, "lower_bound"), C.LitInt 0) )
    | DV_LIML ->
        C.Cast
          (C.Basic "int32_t", C.Index (C.Member (e1, "lower_bound"), C.LitInt 0))
    | ALIMH ->
        let in_ty = get_final_ty env gid nid 0 `In in
        if in_ty <> C.Basic "sisal_array_t" then
          failwith
            (Printf.sprintf
               "Standard ALIMH is not supported under the dope vector backend; \
                please use array_dv instead at gid=%d nid=%d"
               gid nid)
        else
          let leading_sz =
            C.Cond
              ( C.BinOp
                  (C.Gt, C.Index (C.Member (e1, "dims"), C.LitInt 0), C.LitInt 0),
                C.Index (C.Member (e1, "dims"), C.LitInt 0),
                C.Cast (C.Basic "int64_t", C.Member (e1, "size")) )
          in
          C.Cast
            ( C.Basic "int32_t",
              C.BinOp
                ( C.Sub,
                  C.BinOp
                    ( C.Add,
                      C.Index (C.Member (e1, "lower_bound"), C.LitInt 0),
                      leading_sz ),
                  C.LitInt 1 ) )
    | DV_LIMH ->
        let leading_sz =
          C.Cond
            ( C.BinOp
                (C.Gt, C.Index (C.Member (e1, "dims"), C.LitInt 0), C.LitInt 0),
              C.Index (C.Member (e1, "dims"), C.LitInt 0),
              C.Cast (C.Basic "int64_t", C.Member (e1, "size")) )
        in
        C.Cast
          ( C.Basic "int32_t",
            C.BinOp
              ( C.Sub,
                C.BinOp
                  ( C.Add,
                    C.Index (C.Member (e1, "lower_bound"), C.LitInt 0),
                    leading_sz ),
                C.LitInt 1 ) )
    | DV_NUM_RANK -> C.Member (e1, "rank")
    | DV_DIMENSION -> C.Call ("sisal_dv_dimension", [ e2; e1 ])
    | DV_CONFORM -> C.Call ("sisal_dv_conform", [ e1; e2 ])
    | DV_OFFSET_AT -> C.Call ("sisal_dv_offset_at", [ e1; e2; get_in_expr 2 ])
    | DV_RESHAPE_BY_SHAPE -> C.Call ("sisal_array_reshape_by_shape", [ e1; e2 ])
    | TYPECAST -> e1
    | RELEMENTS ->
        let fn = pin.(0) in
        (match e2 with
         | C.Index (C.Cast (_, C.Member (arr, "data")), idx)
           when fn = "lo" || fn = "stride" || fn = "size" ->
             (match fn with
              | "lo" -> C.Index (C.Member (arr, "lower_bound"), idx)
              | "stride" -> C.Index (C.Member (arr, "stride"), idx)
              | "size" -> C.Index (C.Member (arr, "dims"), idx)
              | _ -> assert false)
         | _ ->
             (* Dope-triplet reads collapse: DV_DIMENSION's C value IS already
                the selected component (an int), so RELEMENTS on the {lo,
                stride, size} record is a passthrough -- the pre-records
                contract.  Everything else is a REAL record field read: RAW
                operand (no SISAL_CAST -- a struct needs no scalar cast and its
                inferred port type is unreliable), member selected by the field
                name riding pseudo-port 0. *)
             let in_tyid =
               ES.fold
                 (fun ((_, _), (dn, dp), ty) acc ->
                   if dn = nid && dp = 1 then Some ty else acc)
                 gr.eset None
             in
             let is_dope_triplet =
               match in_tyid with
               | Some t -> (
                   match
                     List.map fst
                       (collect_record_fields (get_typemap_tm gr) t)
                   with
                   | [ "lo"; "stride"; "size" ] -> true
                   | _ -> false)
               | None -> false
             in
             if is_dope_triplet then (
               (* The collapse hard-codes ONE component: sisal_dv_dimension
                  returns a.dims[dim] -- the SIZE.  A lo/stride read off a
                  DV_DIMENSION value would silently get the size instead;
                  no current graph does that (dope-ARRAY triplet loads take
                  the Index-pattern arm above), so keep it impossible. *)
               if fn <> "size" then
                 failwith
                   (Printf.sprintf
                      "RELEMENTS(%s) on a collapsed dope triplet at gid=%d                        nid=%d: only `size` survives the DV_DIMENSION collapse"
                      fn gid nid);
               e2)
             else
               let recv =
                 match
                   ES.fold
                     (fun (src, dst, _) acc ->
                       if dst = (nid, 1) then Some src else acc)
                     gr.eset None
                 with
                 | Some (sn, sp) -> get_expr env gid sn sp `Out
                 | None -> C.LitInt 0
               in
               C.Member (recv, fn))
    | DOT | INNERPRODUCT_NODE ->
        let in_ty = get_final_ty env gid nid 0 `In in
        if in_ty = C.Basic "sisal_array_t" then
          C.Call ("sisal_array_innerproduct", [ e1; e2 ])
        else
          failwith
            (Printf.sprintf
               "DOT/INNERPRODUCT for non-DV types not supported at gid=%d \
                nid=%d"
               gid nid)
    | DV_COMPRESS -> C.Call ("sisal_array_compress", [ e1; e2 ])
    | DV_SORT -> C.Call ("sisal_array_sort", [ e1 ])
    | DV_REVERSE -> C.Call ("sisal_array_reverse", [ e1 ])
    | DV_ROTATE -> C.Call ("sisal_array_rotate", [ e1; e2 ])
    | DV_SLICE -> C.Call ("sisal_array_slice", [ e1; e2; get_in_expr 2 ])
    | GET_DOPE_VEC -> e1
    | DV_RANK_REDUCE ->
        let in_ports =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid then IntSet.add dp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let spec_ports = List.filter (fun p -> p > 0) in_ports in
        if List.length spec_ports = 1 then
          C.Call ("sisal_dv_rank_reduce", [ e1; e2 ])
        else
          let spec_exprs = List.map (fun p -> get_in_expr p) spec_ports in
          let spec_strs = List.map Ir.C_ast_print.string_of_expr spec_exprs in
          let spec_literal =
            Printf.sprintf "(int32_t[]){ %s }" (String.concat ", " spec_strs)
          in
          let rank = List.length spec_ports / 2 in
          C.Call
            ( "sisal_dv_slice",
              [ e1; C.Id spec_literal; C.LitInt rank ] )
    | DV_RANK_REPLACE ->
        C.Call ("sisal_dv_replace_slice", [ e1; e2; get_in_expr 2 ])
    | DV_PERMUTE ->
        (* PERMUTE(A, d0, d1, ...) reorders axes: input port 0 = array, ports 1..rank
         = the new axis order.  Forward ALL the perm indices (variadic), with their
         count, so a rank-k permute/transpose works -- not just the first axis. *)
        let perm_ports =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid && dp >= 1 then IntSet.add dp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let perm_args = List.map (fun p -> get_in_expr p) perm_ports in
        C.Call
          ( "sisal_array_permute",
            e1 :: C.LitInt (List.length perm_args) :: perm_args )
    | DV_SETL | ASETL ->
        C.Call ("sisal_array_setl", [ e1; C.Cast (C.Basic "int64_t", e2) ])
    | AREPLACE ->
        let in_ty = get_final_ty env gid nid 0 `In in
        if in_ty <> C.Basic "sisal_array_t" then
          failwith
            (Printf.sprintf
               "Standard AREPLACE is not supported under the dope vector \
                backend; please use array_dv instead at gid=%d nid=%d"
               gid nid)
        else
          (* A[lo: v1,..,vk] -- values are at ports 2..k+1, placed at consecutive indices
         lo, lo+1, ..., lo+k-1.  Nest single-value replaces (each copies the array),
         so value at port p lands at lo+(p-2).  k=1 is the plain single replace. *)
          let replace_fn p =
            match get_final_ty env gid nid p `In with
            | C.Basic "int32_t" | C.Basic "bool" -> "sisal_array_replace_i32"
            | C.Basic "double" -> "sisal_array_replace_f64"
            (* an array value = a row/slab of a flat 2-D array_dv -> slab replace at the
           leading index (NOT a boxed element; nested array_dv is disallowed) *)
            | C.Basic "sisal_array_t" -> "sisal_dv_replace_slice"
            | _ -> "sisal_array_replace_f32"
          in
          let val_ports =
            ES.fold
              (fun (_, (dn, dp), _) acc ->
                if dn = nid && dp >= 2 then dp :: acc else acc)
              gr.eset []
            |> List.sort_uniq compare
          in
          let lo = C.Cast (C.Basic "int64_t", e2) in
          List.fold_left
            (fun arr_expr p ->
              let off = p - 2 in
              let idx =
                if off = 0 then lo else C.BinOp (C.Add, lo, C.LitInt off)
              in
              C.Call (replace_fn p, [ arr_expr; idx; get_in_expr p ]))
            e1 val_ports
    | DV_REPLACE ->
        let replace_fn p =
          match get_final_ty env gid nid p `In with
          | C.Basic "int32_t" | C.Basic "bool" -> "sisal_array_replace_i32"
          | C.Basic "double" -> "sisal_array_replace_f64"
          | C.Basic "sisal_array_t" -> "sisal_dv_replace_slice"
          | _ -> "sisal_array_replace_f32"
        in
        let val_ports =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid && dp >= 2 then dp :: acc else acc)
            gr.eset []
          |> List.sort_uniq compare
        in
        let lo = C.Cast (C.Basic "int64_t", e2) in
        List.fold_left
          (fun arr_expr p ->
            let off = p - 2 in
            let idx =
              if off = 0 then lo else C.BinOp (C.Add, lo, C.LitInt off)
            in
            C.Call (replace_fn p, [ arr_expr; idx; get_in_expr p ]))
          e1 val_ports
    | DVAADDH | AADDH ->
        (* append e2 at the high end of array e1 -> new array_dv of size+1 *)
        let val_ty = get_final_ty env gid nid 1 `In in
        let fn =
          match val_ty with
          | C.Basic "int32_t" | C.Basic "bool" -> "sisal_array_addh_i32"
          | C.Basic "double" -> "sisal_array_addh_f64"
          | C.Basic "sisal_array_t" -> "sisal_array_addh_arr"
          | _ -> "sisal_array_addh_f32"
        in
        C.Call (fn, [ e1; e2 ])
    | ACATENATE ->
        C.Call ("sisal_array_addh_arr", [ e1; e2 ])
    | DVAADDL ->
        (* prepend e2 at the low end of array e1 -> new array_dv of size+1 *)
        let val_ty = get_final_ty env gid nid 1 `In in
        let fn =
          match val_ty with
          | C.Basic "int32_t" | C.Basic "bool" -> "sisal_array_addl_i32"
          | C.Basic "double" -> "sisal_array_addl_f64"
          | C.Basic "sisal_array_t" -> "sisal_array_addl_arr"
          | _ -> "sisal_array_addl_f32"
        in
        C.Call (fn, [ e1; e2 ])
    | DVAFILL ->
        (* array_fill(lo, hi, val) -> new array [lo..hi], every element = val *)
        let e3 = get_in_expr 2 in
        let val_ty = get_final_ty env gid nid 2 `In in
        if is_struct_cty val_ty then
          let out_ty_id =
            ES.fold
              (fun ((sn, sp), _, t) acc ->
                if sn = nid && sp = 0 && t <> 0 then Some t else acc)
              gr.eset None
            |> Option.value ~default:0
          in
          C.Call
            ( "sisal_array_fill_rec",
              [
                C.Cast (C.Basic "int64_t", e1);
                C.Cast (C.Basic "int64_t", e2);
                e3;
                C.LitInt out_ty_id;
              ] )
        else
          let fn =
            match val_ty with
            | C.Basic "int32_t" | C.Basic "bool" -> "sisal_array_fill_i32"
            | C.Basic "double" -> "sisal_array_fill_f64"
            | C.Basic "sisal_array_t" -> "sisal_array_fill_arr"
            | _ -> "sisal_array_fill_f32"
          in
          C.Call
            ( fn,
              [
                C.Cast (C.Basic "int64_t", e1); C.Cast (C.Basic "int64_t", e2); e3;
              ] )
    | DVABUILD | ABUILD ->
        let get_raw_in_expr p =
          let producers =
            ES.fold
              (fun (src, dst, _) acc ->
                if dst = (nid, p) then Some src else acc)
              gr.eset None
          in
          match producers with
          | Some (sn, sp) -> get_expr env gid sn sp `Out
          | None -> C.LitInt 0
        in
        let out_tyid =
          ES.fold
            (fun ((sn, sp), _, ty) acc ->
              if sn = nid && sp = 0 then ty else acc)
            gr.eset 0
        in
        let elem_tid =
          match TM.find_opt out_tyid env.tm with
          | Some (Array_dv e) | Some (Array_ty e) -> e
          | _ -> 4
        in
        let in_ports =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid then IntSet.add dp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let el_ports = List.filter (fun p -> p > 0) in_ports in
        let el_exprs = List.map get_raw_in_expr el_ports in
        if el_exprs = [] then
          C.Call
            ( "sisal_array_alloc_empty",
              [
                C.LitInt 1;
                C.LitInt elem_tid;
                C.Cast (C.Basic "uint64_t", C.LitInt 0);
              ] )
        else
          let is_arr_elem =
            let sn, sp =
              match
                ES.fold
                  (fun (src, dst, _) acc ->
                    if dst = (nid, List.hd el_ports) then Some src else acc)
                  gr.eset None
              with
              | Some (sn, sp) -> (sn, sp)
              | None -> (0, 0)
            in
            let prod_ty = get_final_ty env gid sn sp `Out in
            match prod_ty with C.Basic "sisal_array_t" -> true | _ -> false
          in
          (* Element C type from the typemap id (NOT an ad-hoc id match --
             the old 6/4-only dispatch sent float/bool/int64 literals through
             the sisal_array_t staging array, a miscompile).  Boxed
             array-valued elements keep sisal_array_build_arr (it flattens);
             everything else uses the generic templated builder, type_id
             recorded in the dope. *)
          let elem_c_ty =
            if is_arr_elem then "sisal_array_t"
            else
              Ir.C_ast_print.string_of_c_type
                (c_type_of_if1_tyid (get_typemap_tm gr) elem_tid)
          in
          let e_lb = get_raw_in_expr 0 in
          (* per-element cast to the staging type: C++ brace init rejects
             narrowing (double-typed intermediates into a float array) *)
          let elem_strs =
            List.map
              (fun e ->
                Printf.sprintf "(%s)(%s)" elem_c_ty
                  (Ir.C_ast_print.string_of_expr e))
              el_exprs
          in
          let elems_formatted = String.concat ", " elem_strs in
          let call_str =
            if is_arr_elem then
              Printf.sprintf "sisal_array_build_arr(%s, %d, __arr)"
                (Ir.C_ast_print.string_of_expr e_lb)
                (List.length el_exprs)
            else
              Printf.sprintf "sisal_array_build_elems(%s, %d, __arr, %d)"
                (Ir.C_ast_print.string_of_expr e_lb)
                (List.length el_exprs) elem_tid
          in
          let lambda_str =
            Printf.sprintf
              "([&]() -> sisal_array_t { const %s __arr[] = {%s}; return \
               %s; })()"
              elem_c_ty elems_formatted call_str
          in
          C.Id lambda_str
    | DVAADJUST ->
        (* array_adjust(A, lo, hi) -- window slice A[lo..hi].  Args wired reversed:
         port 0 = hi (e1), port 1 = lo (e2), port 2 = A. *)
        C.Call
          ( "sisal_array_adjust",
            [
              get_in_expr 2;
              C.Cast (C.Basic "int64_t", e2);
              C.Cast (C.Basic "int64_t", e1);
            ] )
    | PAD_NODE ->
        C.Call ("sisal_array_pad", [ e1; e2; get_in_expr 2; get_in_expr 3 ])
    | STENCIL_NODE -> C.Call ("sisal_array_stencil", [ e1; e2; get_in_expr 2 ])
    | WHERE_NODE -> C.Call ("sisal_array_where", [ e1; e2; get_in_expr 2 ])
    | NONZERO_NODE -> C.Call ("sisal_array_nonzero", [ e1 ])
    | REDUCE_ALL ->
        let fname =
          List.find_map (function Name n -> Some n | _ -> None) pr
          |> Option.map String.lowercase_ascii
          |> Option.value ~default:"sum"
        in
        let reduce_fn =
          match (fname, t_res) with
          | "sum", C.Basic "double" -> "sisal_array_reduce_double_sum"
          | "sum", C.Basic "float" -> "sisal_array_reduce_sum"
          | "sum", C.Basic "int32_t" -> "sisal_array_reduce_int_sum"
          | "product", C.Basic "double" -> "sisal_array_reduce_double_product"
          | "product", C.Basic "float" -> "sisal_array_reduce_float_product"
          | "product", C.Basic "int32_t" -> "sisal_array_reduce_int_product"
          | "least", C.Basic "double" -> "sisal_array_reduce_double_least"
          | "least", C.Basic "float" -> "sisal_array_reduce_least"
          | "least", C.Basic "int32_t" -> "sisal_array_reduce_int_least"
          | "greatest", C.Basic "double" -> "sisal_array_reduce_double_greatest"
          | "greatest", C.Basic "float" -> "sisal_array_reduce_greatest"
          | "greatest", C.Basic "int32_t" -> "sisal_array_reduce_int_greatest"
          | _ -> "sisal_array_reduce_double_sum"
        in
        C.Call (reduce_fn, [ e1 ])
    | INVOCATION ->
        let fname_pragma =
          List.find_map (function Name n -> Some n | _ -> None) pr
        in
        let fname, start_port =
          match fname_pragma with
          | Some n -> ("func_" ^ String.uppercase_ascii n, 0)
          | None -> (
              match
                ES.fold
                  (fun (src, dst, _) acc ->
                    if dst = (nid, 0) then Some src else acc)
                  gr.eset None
              with
              | Some (0, pn) -> (
                  match IntMap.find_opt pn env.proc_map with
                  | Some name -> (name, 1)
                  | _ -> ("func_UNKNOWN", 1))
              | _ -> ("func_UNKNOWN", 1))
        in
        let in_ports =
          ES.fold
            (fun (_, (dn, dp), _) acc ->
              if dn = nid then IntSet.add dp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let args =
          List.filter_map
            (fun pid ->
              if pid < start_port then None else Some (get_in_expr pid))
            in_ports
        in
        C.Call (fname, args)
    | FINALVALUE -> e1
    (* DV_GATHER inside a for-initial RETURNS is realized specially by
     lower_for_initial (alloc-before-loop + per-iteration store); this generic
     placeholder only keeps lower_graph from aborting, and the RETURNS port is
     re-bound to the gather array afterwards.  DV_MAKE_DOPE (the shaped
     gather's dope source) likewise: its extent operands are read structurally
     off the RETURNS graph by the gather realization, never evaluated here. *)
    | DV_GATHER | AGATHER | DV_MAKE_DOPE | DV_SCATTER_AT -> e1
    | RBUILD -> (
        (* Record or Union construction.
           For records: C++ aggregate init `struct_rec_N{f0, ..}`.
           For unions: Call inline constructor helper `make_union_N_Tag(val)`. *)
        let out_tyid =
          ES.fold
            (fun ((sn, sp), _, ty) acc ->
              if sn = nid && sp = 0 then Some ty else acc)
            gr.eset None
        in
        let tm = get_typemap_tm gr in
        let raw_in k =
          match
            ES.fold
              (fun (src, dst, _) acc ->
                if dst = (nid, k) then Some src else acc)
              gr.eset None
          with
          | Some (sn, sp) -> get_expr env gid sn sp `Out
          | None -> C.LitInt 0
        in
        match out_tyid with
        | Some tid -> (
            let tid =
              match TM.find_opt tid !Apple_helpers.global_alias_map with
              | Some leader -> leader
              | None -> tid
            in
            match TM.find_opt tid tm with
            | Some (Record _) -> (
                match c_type_of_if1_tyid tm tid with
                | C.Basic nm
                  when String.length nm > 7 && String.sub nm 0 7 = "struct " ->
                    let sname = String.sub nm 7 (String.length nm - 7) in
                    let fields = collect_record_fields tm tid in
                    let args =
                      List.mapi (fun k (_, fty) -> C.Cast (fty, raw_in k)) fields
                    in
                    C.BraceInit (sname, args)
                | _ ->
                    failwith
                      (Printf.sprintf
                         "RBUILD at gid=%d nid=%d: record type %d has invalid C type"
                         gid nid tid))
            | Some (Union _) ->
                let tag_name =
                  if Array.length pin > 1 && pin.(1) <> "" then pin.(1)
                  else if Array.length pin > 0 && pin.(0) <> "" then pin.(0)
                  else "UNKNOWN_TAG"
                in
                let val_expr = raw_in 0 in
                C.Call ("make_union_" ^ string_of_int tid ^ "_" ^ tag_name, [ val_expr ])
            | _ ->
                failwith
                  (Printf.sprintf
                     "RBUILD at gid=%d nid=%d: output type %d is not a record/union"
                     gid nid tid))
        | None ->
            failwith
              (Printf.sprintf "RBUILD at gid=%d nid=%d: no output edge" gid nid)
        )
    | RREPLACE -> (
        (* Functional field update `r replace [f: v]`: rebuild the whole
           struct -- every field copied from the operand except the named one
           substituted.  Pure expression (BraceInit), no temp needed; the
           operand is a variable, so per-field member reads don't recompute.
           Ports: 0 = record, 2 = new value; field name rides pseudo-port 1. *)
        let fn = pin.(1) in
        let out_tyid =
          ES.fold
            (fun ((sn, sp), _, ty) acc ->
              if sn = nid && sp = 0 then Some ty else acc)
            gr.eset None
        in
        let tm = get_typemap_tm gr in
        let raw_in k =
          match
            ES.fold
              (fun (src, dst, _) acc ->
                if dst = (nid, k) then Some src else acc)
              gr.eset None
          with
          | Some (sn, sp) -> get_expr env gid sn sp `Out
          | None -> C.LitInt 0
        in
        match out_tyid with
        | Some tid -> (
            match c_type_of_if1_tyid tm tid with
            | C.Basic nm
              when String.length nm > 7 && String.sub nm 0 7 = "struct " ->
                let sname = String.sub nm 7 (String.length nm - 7) in
                let fields = collect_record_fields tm tid in
                if not (List.mem_assoc fn fields) then
                  failwith
                    (Printf.sprintf
                       "RREPLACE at gid=%d nid=%d: no field `%s` in %s" gid
                       nid fn nm);
                let recv = raw_in 0 and newv = raw_in 2 in
                let args =
                  List.map
                    (fun (name, fty) ->
                      if name = fn then C.Cast (fty, newv)
                      else C.Member (recv, name))
                    fields
                in
                C.BraceInit (sname, args)
            | _ ->
                failwith
                  (Printf.sprintf
                     "RREPLACE at gid=%d nid=%d: output type %d is not a \
                      record"
                     gid nid tid))
        | None ->
            failwith
              (Printf.sprintf "RREPLACE at gid=%d nid=%d: no output edge" gid
                 nid))
    | sym ->
        failwith
          (Printf.sprintf
             "Unsupported IF1 Simple node symbol at gid=%d nid=%d: %s" gid nid
             (string_of_node_sym sym))
  in
  (* For an INVOCATION of a multi-RETURN function, unpack the returned struct.
     Gate on the CALLEE's declared arity (does it return a *_results record?),
     NOT on the count of live output edges: a dead/unused output would otherwise
     drop the live count to 1 and route a record-returning call through the
     single-value cast path (casting the whole record -> type error / dropped out). *)
  let stmts, e' =
    match sym with
    | INVOCATION ->
        let out_ports =
          ES.fold
            (fun ((sn, sp), _, _) acc ->
              if sn = nid then IntSet.add sp acc else acc)
            gr.eset IntSet.empty
          |> IntSet.elements
        in
        let callee_name =
          match rhs with C.Call (fn, _) -> Some fn | _ -> None
        in
        let callee_arity =
          match callee_name with
          | Some fn ->
              IntMap.fold
                (fun pnid pname acc ->
                  if pname = fn then
                    match IntMap.find_opt pnid env.procedures_info with
                    | Some sub ->
                        ES.fold
                          (fun (_, (dn, dp), ty) a ->
                            if dn = 0 && not (is_error_port ty sub) then
                              IntSet.add dp a
                            else a)
                          sub.eset IntSet.empty
                        |> IntSet.cardinal
                    | None -> acc
                  else acc)
                env.proc_map 0
          | None -> 0
        in
        if callee_arity > 1 then begin
          let struct_name =
            match callee_name with
            | Some fn -> Printf.sprintf "%s_results" (String.uppercase_ascii fn)
            | None -> "UNKNOWN_results"
          in
          let tmp =
            Printf.sprintf "_mr_%s_%d" (scope_of env.gid_name_map gid) nid
          in
          let decl_tmp =
            C.Decl (C.Basic ("struct " ^ struct_name), tmp, Some rhs)
          in
          (* extract .res_<port> for each LIVE output port (dead ones bind nothing) *)
          List.fold_left
            (fun (acc, e) port ->
              let field = C.Member (C.Id tmp, Printf.sprintf "res_%d" port) in
              let ss, e' = assign_with_cast e gid nid port `Out field in
              (acc @ ss, e'))
            ([ decl_tmp ], env) out_ports
        end
        else assign_with_cast env gid nid 0 `Out rhs
    | GET_DOPE_VEC ->
        let ss0, e' = assign_with_cast env gid nid 0 `Out rhs in
        let ss1, e'' = assign_with_cast e' gid nid 1 `Out rhs in
        (ss0 @ ss1, e'')
    | _ -> assign_with_cast env gid nid 0 `Out rhs
  in
  (stmts, e')

(** [lower_if_graph env parent_gr nid loop_gr loop_gid] — an IF/SELECT
    compound to a C if/else: lower the PREDICATE subgraph, then each arm's
    subgraph inside its branch, and merge arm results by assigning both arms'
    values to the compound's shared output variables (the phi). *)
and lower_if_graph env parent_gr nid loop_gr loop_gid =
  let gid = env.curr_gid in
  let env_loop_base =
    {
      env with
      parent_env = Some env;
      compound_nid_in_parent = nid;
      curr_gid = loop_gid;
      curr_gr = loop_gr;
    }
  in
  let env_loop_base = scan_fanout loop_gr loop_gid env_loop_base in
  let node =
    match NM.find_opt nid parent_gr.nmap with
    | Some n -> n
    | _ -> failwith "no node"
  in
  let decl_stmts, env_loop_base =
    declare_outputs env_loop_base parent_gr gid nid node
  in
  (* The IF compound's output ports -- every branch assigns into these (declared
     once by declare_outputs above, so the if/else blocks just assign). *)
  let if_out_pids =
    ES.fold
      (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc)
      parent_gr.eset IntSet.empty
    |> IntSet.elements
  in
  (* Assign a branch graph's boundary outputs to the IF compound's outputs. *)
  let assign_if_outs e br_gr br_gid =
    List.fold_left
      (fun (acc, e) dp ->
        let src_opt =
          match FullPortMap.find_opt (br_gid, 0, dp, `In) e.var_map with
          | Some _ as found -> found
          | None -> (
              match
                ES.fold
                  (fun (src, dst, _) a -> if dst = (0, dp) then Some src else a)
                  br_gr.eset None
              with
              | Some (sn, sp) ->
                  FullPortMap.find_opt (br_gid, sn, sp, `Out) e.var_map
              | None -> None)
        in
        match src_opt with
        | Some src_expr ->
            let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
            (acc @ stmts, e')
        | None -> (acc, e))
      ([], { e with curr_gid = gid; curr_gr = parent_gr })
      if_out_pids
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
        let pgid =
          try GidMap.find (ggid, pred_cid) e.gid_table with _ -> -1
        in
        let env_pred =
          {
            e with
            parent_env = Some e;
            curr_gid = pgid;
            curr_gr = pred_sg;
            parent_map = IntMap.add pgid (ggid, pred_cid) e.parent_map;
          }
        in
        let pred_stmts, e_pred = lower_graph env_pred g pred_cid pred_sg pgid in
        let v_pred =
          match
            ES.fold
              (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc)
              pred_sg.eset None
          with
          | Some (sn, sp) -> get_expr e_pred pgid sn sp `Out
          | None -> C.LitInt 0
        in
        let e =
          {
            e with
            var_map = e_pred.var_map;
            type_table = e_pred.type_table;
            seen_decls = e_pred.seen_decls;
          }
        in
        (* lower_chain returns env with curr_gid reset to the outer `gid`; restore
           the current if-level (`ggid`/`g`) before each branch so its boundary
           copy-in resolves against THIS scope, not the outer one. *)
        let at_level e = { e with curr_gid = ggid; curr_gr = g } in
        let then_cid, then_sg =
          match find_subgraph g "THEN" with
          | Some x -> x
          | _ -> failwith "no THEN"
        in
        let tgid =
          try GidMap.find (ggid, then_cid) e.gid_table with _ -> -1
        in
        let e = at_level e in
        let then_stmts, e =
          lower_chain
            {
              e with
              parent_env = Some e;
              curr_gid = tgid;
              curr_gr = then_sg;
              parent_map = IntMap.add tgid (ggid, then_cid) e.parent_map;
            }
            g then_cid then_sg tgid
        in
        let else_cid, else_sg =
          match find_subgraph g "ELSE" with
          | Some x -> x
          | _ -> failwith "no ELSE"
        in
        let egid =
          try GidMap.find (ggid, else_cid) e.gid_table with _ -> -1
        in
        let e = at_level e in
        let else_stmts, e =
          lower_chain
            {
              e with
              parent_env = Some e;
              curr_gid = egid;
              curr_gr = else_sg;
              parent_map = IntMap.add egid (ggid, else_cid) e.parent_map;
            }
            g else_cid else_sg egid
        in
        ( in_stmts
          @ [
              C.Compound (pred_stmts @ [ C.If (v_pred, then_stmts, else_stmts) ]);
            ],
          { e with curr_gid = gid; curr_gr = parent_gr } )
  in
  let body, e_final =
    lower_chain env_loop_base parent_gr nid loop_gr loop_gid
  in
  (decl_stmts @ body, { e_final with curr_gid = gid; curr_gr = parent_gr })

(** [lower_tagcase env parent_gr nid loop_gr loop_gid] — a TAGCASE compound:
    dispatch on the union value's runtime tag, bind the selected payload into
    the chosen arm's scope, lower each arm's subgraph in its branch, and merge
    arm outputs into the compound's output variables.  Union type ids resolve
    through global_alias_map (dedup'd union ids -> leader). *)
and lower_tagcase env parent_gr nid loop_gr loop_gid =
  let gid = env.curr_gid in
  let tm = get_typemap_tm parent_gr in
  let node =
    match NM.find_opt nid parent_gr.nmap with
    | Some n -> n
    | _ -> failwith "no node"
  in
  let decl_stmts, env =
    declare_outputs env parent_gr gid nid node
  in
  let union_expr, union_tyid =
    match
      ES.fold
        (fun (src, dst, ty) acc ->
          if fst dst = nid then
            let ty =
              match TM.find_opt ty !Apple_helpers.global_alias_map with
              | Some leader -> leader
              | None -> ty
            in
            match TM.find_opt ty tm with
            | Some (Union _) -> Some (get_expr env gid (fst src) (snd src) `Out, ty)
            | _ -> acc
          else acc)
        parent_gr.eset None
    with
    | Some (expr, ty) -> (expr, ty)
    | None -> failwith (Printf.sprintf "TAGCASE at nid=%d: union input not found" nid)
  in
  let tags = Apple_helpers.collect_union_tags_with_ids tm union_tyid in
  let assoc_lis =
    match node with
    | Compound (_, _, _, _, _, assoc_lis) -> assoc_lis
    | _ -> assert false
  in
  let tag_mappings =
    List.mapi (fun idx (tag_id, tname, tty) ->
      let dest_nid = List.nth assoc_lis idx in
      (idx, tag_id, tname, tty, dest_nid)
    ) tags
  in
  let unique_arms =
    List.fold_left
      (fun acc (idx, tag_id, tname, tty, dest_nid) ->
        let existing = try List.assoc dest_nid acc with Not_found -> [] in
        (dest_nid, (idx, tag_id, tname, tty) :: existing) :: List.remove_assoc dest_nid acc)
      [] tag_mappings
  in
  let switch_cases =
    List.map (fun (dest_nid, cases) ->
      let arm_node =
        match NM.find_opt dest_nid loop_gr.nmap with
        | Some (Compound (cid, _, _, pr, arm_gr, _)) -> (cid, arm_gr, pr)
        | _ -> failwith (Printf.sprintf "TAGCASE: arm node %d not found" dest_nid)
      in
      let cid, arm_gr, pr = arm_node in
      let sub_gid = try GidMap.find (loop_gid, dest_nid) env.gid_table with _ -> -1 in
      let is_otherwise =
        List.exists (function Name "Otherwise" -> true | _ -> false) pr
      in
      let env_child =
        {
          env with
          parent_env = Some env;
          compound_nid_in_parent = dest_nid;
          curr_gid = sub_gid;
          curr_gr = arm_gr;
          parent_map = IntMap.add sub_gid (loop_gid, dest_nid) env.parent_map;
        }
      in
      let env_child = scan_fanout arm_gr sub_gid env_child in
      let pre_decl, env_child = pre_declare_graph_locals env_child arm_gr sub_gid in
      let payload_init_stmt, env_child =
        if is_otherwise then ([], env_child)
        else
          let (_, tag_id, tname, tty) = List.hd cases in
          let p_type = tty in
          let p_var = Printf.sprintf "v_%s_n__0_p0_i" (scope_of env.gid_name_map sub_gid) in
          let p_expr = C.Member (union_expr, "val." ^ tname) in
          let stmt = C.Decl (p_type, p_var, Some p_expr) in
          let env_child =
            {
              env_child with
              var_map = FullPortMap.add (sub_gid, 0, 0, `Out) (C.Id p_var) env_child.var_map
            }
          in
          ([ stmt ], env_child)
      in
      let other_in_stmts, env_child =
        let init_ports_res =
          if env_child.parent_env = None || IntMap.mem sub_gid env_child.proc_map then ([], env_child)
          else init_boundary_ports env_child loop_gr dest_nid arm_gr sub_gid
        in
        let stmts, e = init_ports_res in
        let filtered_stmts =
          List.filter (fun stmt ->
            match stmt with
            | C.Decl (_, var_name, _) ->
                let p_var = Printf.sprintf "v_%s_n__0_p0_i" (scope_of env.gid_name_map sub_gid) in
                var_name <> p_var
            | _ -> true
          ) stmts
        in
        (filtered_stmts, e)
      in
      let body_stmts, env_child =
        let sorted = topo_sort arm_gr in
        let rec walk covered acc e = function
          | [] -> (acc, e)
          | nid :: rest when IntSet.mem nid covered -> walk covered acc e rest
          | 0 :: rest -> walk covered acc e rest
          | nid :: rest -> (
              match NM.find_opt nid arm_gr.nmap with
              | Some (Literal (_, code, value, _)) ->
                  let lit =
                    match code with
                    | REAL | DOUBLE -> C.LitFloat (float_of_string value)
                    | BOOLEAN -> C.Id (String.lowercase_ascii value)
                    | _ -> try C.LitInt (int_of_string value) with _ -> C.LitInt 0
                  in
                  let ss, e' = assign_with_cast e sub_gid nid 0 `Out lit in
                  walk covered (acc @ ss) e' rest
              | Some node ->
                  let ss, e' = lower_node e arm_gr nid node in
                  walk covered (acc @ ss) e' rest
              | None -> walk covered acc e rest)
        in
        walk IntSet.empty [] env_child sorted
      in
      let arm_out_pids =
        ES.fold
          (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc)
          parent_gr.eset IntSet.empty
        |> IntSet.elements
      in
      let out_prop_stmts, _ =
        List.fold_left
          (fun (acc, e) dp ->
            let src_opt =
              match FullPortMap.find_opt (sub_gid, 0, dp + 1, `In) env_child.var_map with
              | Some _ as found -> found
              | None -> (
                  match
                    ES.fold
                      (fun (src, dst, _) a -> if dst = (0, dp + 1) then Some src else a)
                      arm_gr.eset None
                  with
                  | Some (sn, sp) ->
                      FullPortMap.find_opt (sub_gid, sn, sp, `Out) env_child.var_map
                  | None -> None)
            in
            match src_opt with
            | Some src_expr ->
                let ss, e' = assign_with_cast e gid nid dp `Out src_expr in
                (acc @ ss, e')
            | None -> (acc, e))
          ([], env_child) arm_out_pids
      in
      let arm_body =
        pre_decl @ payload_init_stmt @ other_in_stmts @ body_stmts @ out_prop_stmts @ [ C.Break ]
      in
      let labels_str =
        if is_otherwise then "default"
        else
          List.map (fun (_, tag_id, name, _) ->
            Printf.sprintf "case union_%d_%s" union_tyid name
          ) cases
          |> String.concat ":\n"
      in
      let arm_str =
        Printf.sprintf "%s: {\n%s\n}"
          labels_str
          (Ir.C_ast_print.string_of_stmt 2 (C.Compound arm_body))
      in
      arm_str
    ) unique_arms
  in
  let switch_stmt_str =
    Printf.sprintf "switch (%s.tag) {\n  %s\n}"
      (Ir.C_ast_print.string_of_expr union_expr)
      (String.concat "\n  " switch_cases)
  in
  (decl_stmts @ [ C.Raw switch_stmt_str ], env)

(** [lower_forall env gr gid nid loop_gr sub_gid pr] — a FORALL compound to
    C loops.  Generator nest -> counted for-loops (extents/lb read off the
    RANGEGENs); BODY lowered inline; RETURNS realized PER OUTPUT PORT:
    reductions accumulate, FINALVALUE keeps the last value, gathers allocate
    up front (extent product) and store at the flat counter, DV_SCATTER_AT
    stores at the placement coordinates instead, array-valued gathers box
    descriptors then re-pack flat (rank read off the first element at
    runtime).  Masked reductions guard their accumulation with the `when`
    filter port. *)
and lower_forall env gr gid nid loop_gr sub_gid pr =
  (* ===== FRESH forall -> C lowering (rebuilt from scratch) =====
     Step 1: locate the GENERATOR / BODY / RETURNS subgraph nodes inside loop_gr
     via a node-map walk.  (NM-walk is fine HERE -- we are only FINDING the three
     structural children of the forall, not lowering anything yet.)  Everything
     else is built up step by step.  (The previous recursive `zip_loops` version
     was removed once this path had soaked.) *)
  let _ = (nid, sub_gid, pr) in
  let find_role role =
    NM.fold
      (fun n node acc ->
        match acc with
        | Some _ -> acc
        | None -> (
            match node with
            | Compound (_, _, _, prag, sub, _)
              when get_compound_type prag = role ->
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
    {
      env with
      parent_env = Some env;
      compound_nid_in_parent = nid;
      curr_gid = sub_gid;
      curr_gr = loop_gr;
    }
  in
  let _ = env_loop in
  (* outer value feeding the forall compound's input port k (boundary imports) *)
  let parent_feed k =
    match
      ES.fold
        (fun ((sn, sp), (dn, dp), _) acc ->
          if dn = nid && dp = k then Some (sn, sp) else acc)
        gr.eset None
    with
    | Some (sn, sp) -> Some (get_expr env gid sn sp `Out)
    | None -> None
  in
  (* The anticipatory list, as a binding tracker: every declared slot is recorded
     in var_map keyed by (gid, val_def, def_port, `Out) so later lowering can
     RESOLVE a port to its slot name -- or OVERRIDE it (relays). *)
  let rec collect g ggid (acc, seen, e) =
    let tm = get_typemap_tm g in
    let cty_of v = c_type_of_if1_tyid tm v.val_ty in
    let cs, _ = g.symtab in
    let acc, seen, e =
      SM.fold
        (fun _ v (acc, seen, e) ->
          let cname =
            get_c_name e.proc_map e.gid_name_map ggid v.val_def v.def_port `Out
              g
          in
          if StringSet.mem cname seen then (acc, seen, e)
          else
            let init =
              if ggid = sub_gid && v.val_def = 0 then parent_feed v.def_port
              else None
            in
            let e =
              {
                e with
                var_map =
                  FullPortMap.add
                    (ggid, v.val_def, v.def_port, `Out)
                    (C.Id cname) e.var_map;
              }
            in
            ( acc @ [ C.Decl (cty_of v, cname, init) ],
              StringSet.add cname seen,
              e ))
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
  let sym_decls, seen2, env_loop =
    collect loop_gr sub_gid ([], StringSet.empty, env_loop)
  in
  (* Supplement: bind EVERY parent-fed forall boundary port not covered by the
     symtab walk.  Scatter extents arrive as UNNAMED boundary entries (the
     triple-based extent plumbing registers nothing in symtabs), so their
     value would otherwise never be declared. *)
  let sym_decls, seen2, env_loop =
    ES.fold
      (fun ((sn, sp), (dn, dp), tyid) (decls, seen, e) ->
        if dn <> nid then (decls, seen, e)
        else if FullPortMap.mem (sub_gid, 0, dp, `Out) e.var_map then
          (decls, seen, e)
        else
          let cname =
            get_c_name e.proc_map e.gid_name_map sub_gid 0 dp `Out loop_gr
          in
          if StringSet.mem cname seen then (decls, seen, e)
          else
            let cty = c_type_of_if1_tyid env.tm tyid in
            let init = Some (get_expr env gid sn sp `Out) in
            let e =
              {
                e with
                var_map =
                  FullPortMap.add (sub_gid, 0, dp, `Out) (C.Id cname) e.var_map;
                type_table =
                  FullPortMap.add (sub_gid, 0, dp, `Out) cty e.type_table;
              }
            in
            (decls @ [ C.Decl (cty, cname, init) ], StringSet.add cname seen, e))
      gr.eset (sym_decls, seen2, env_loop)
  in
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
     GENERATORs' copy-ins are emitted by lower_gen INSIDE the parent loop (a
     nested bound may reference the enclosing axis, Fortran-DO style); only the
     TOP generator's copy-ins are loop-invariant and sit before the loops. *)
  let gen_gid_of pg gnid =
    try GidMap.find (pg, gnid) env.gid_table with _ -> -1
  in
  (* Fortran-DO dependent ranges (`for i in 1,n cross j in i,n`): a nested
     level's BOUND reads an enclosing axis, so the nest is NOT rectangular.
     NB an axis value merely relayed through the nested boundary to the BODY
     (every rectangular cross does that) is not dependence — only taint that
     reaches a RANGEGEN/scatter INPUT counts.  Propagate taint forward from
     axis outputs (through bound math and nested boundaries, in topo order);
     `timports` = tainted boundary IN ports of the current level.  Decides
     (a) whether nested copy-ins may be hoisted to the preheader
     (rectangular only) and (b) how the gather allocates (extent product vs
     a counting pre-nest, below). *)
  let rec nest_is_dependent g timports =
    let is_axis n =
      match NM.find_opt n g.nmap with
      | Some (Simple (_, (RANGEGEN | DV_SCATTER | ASCATTER), _, _, _)) -> true
      | _ -> false
    in
    let src_tainted tset sn sp =
      (sn = 0 && IntSet.mem sp timports) || IntSet.mem sn tset
    in
    let tainted =
      List.fold_left
        (fun tset n ->
          if is_axis n then IntSet.add n tset
          else if
            ES.exists
              (fun ((sn, sp), (dn, _), _) -> dn = n && src_tainted tset sn sp)
              g.eset
          then IntSet.add n tset
          else tset)
        IntSet.empty (topo_sort g)
    in
    ES.exists
      (fun ((sn, sp), (dn, _), _) ->
        is_axis dn && src_tainted tainted sn sp)
      g.eset
    ||
    match find_subgraph g "GENERATOR" with
    | Some (ign, igr) ->
        let timports' =
          ES.fold
            (fun ((sn, sp), (dn, dp), _) acc ->
              if dn = ign && src_tainted tainted sn sp then IntSet.add dp acc
              else acc)
            g.eset IntSet.empty
        in
        nest_is_dependent igr timports'
    | None -> false
  in
  let dependent =
    match _generator with
    | Some (_, gen_gr) -> nest_is_dependent gen_gr IntSet.empty
    | None -> false
  in
  let rec relay_copyins parent_g parent_nid parent_gid g ggid =
    let in_ports =
      ES.fold
        (fun ((sn, sp), _, _) acc -> if sn = 0 then IntSet.add sp acc else acc)
        g.eset IntSet.empty
    in
    let here =
      IntSet.fold
        (fun k acc ->
          match
            ES.fold
              (fun ((sn, sp), (dn, dp), _) acc ->
                if dn = parent_nid && dp = k then Some (sn, sp) else acc)
              parent_g.eset None
          with
          | Some (sn, sp) ->
              let parent_expr = get_expr env_loop parent_gid sn sp `Out in
              let dst =
                get_c_name env.proc_map env.gid_name_map ggid 0 k `Out g
              in
              acc @ [ C.Expr (C.BinOp (C.Assign, C.Id dst, parent_expr)) ]
          | None -> acc)
        in_ports []
    in
    (* RECTANGULAR nest: nested copy-ins are loop-invariant, hoist them here
       too — the preheader gather alloc reads inner boundary slots via
       collect_extents.  DEPENDENT nest: they are NOT invariant (a bound
       reads an enclosing axis), so they exist only per-iteration, emitted
       by lower_gen INSIDE the parent loop via ~before. *)
    let nested =
      if dependent then []
      else
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
        relay_copyins loop_gr gen_nid sub_gid gen_gr
          (gen_gid_of sub_gid gen_nid)
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
    let port_cty n p =
      match
        ES.fold
          (fun ((sn, sp), _, t) acc ->
            if sn = n && sp = p && t <> 0 then Some t else acc)
          g.eset None
      with
      | Some t -> c_type_of_if1_tyid env_loop.tm t
      | None -> C.Basic "int32_t"
    in
    let bind e n p =
      {
        e with
        var_map = FullPortMap.add (ggid, n, p, `Out) (C.Id (slot n p)) e.var_map;
      }
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
              (pre, rs, ss @ [ (n, `Dv) ], bind (bind e n 0) n 1)
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
        ES.fold
          (fun ((sn, sp), (dn, dp), _) acc ->
            if dn = n && dp = p then Some (sn, sp) else acc)
          g.eset None
      with
      | Some (sn, sp) -> get_expr env_g ggid sn sp `Out
      | None -> C.LitInt 0
    in
    (* recurse into a nested GENERATOR (cross): its boundary copy-ins execute
       HERE, per iteration of THIS level, before the inner loop -- a nested
       bound may read this axis's variable (dependent range, Fortran-DO
       semantics; nest_is_dependent in lower_forall detects that case). *)
    let inner' =
      match find_subgraph g "GENERATOR" with
      | Some (ign, igr) ->
          let igid = gen_gid_of ggid ign in
          let cis = relay_copyins g ign ggid igr igid in
          lower_gen ~before:cis igr igid inner
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
              [
                C.Expr (C.BinOp (C.Assign, C.Id (slot ax 1), resolve_in ax 0));
                C.Expr (C.BinOp (C.Assign, C.Id (slot ax 2), resolve_in ax 1));
              ])
            (prim :: sibs)
        in
        (* dot siblings advance in lockstep: sib = sib_lb + (primary - primary_lb) *)
        let sib_decls =
          List.map
            (fun s ->
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     C.Id (slot s 0),
                     C.BinOp
                       (C.Add, resolve_in s 0, C.BinOp (C.Sub, C.Id it, lb)) )))
            sibs
        in
        (* `before` (copy-ins for a nested level / allocs at the top) must
           precede bound_outs: a dependent nested bound's re-export reads the
           copied-in slot of THIS iteration, not the previous one. *)
        pre @ before @ bound_outs
        @ [
            C.For
              ( C.Expr (C.BinOp (C.Assign, C.Id it, lb)),
                C.BinOp (C.Le, C.Id it, ub),
                C.UnaryOp (C.PostInc, C.Id it),
                sib_decls @ inner' );
          ]
    | [], (pn, _) :: _ ->
        (* element scatter (dot of scatters share one counter k over the array) *)
        let k = Printf.sprintf "__k_%d" ggid in
        let parr = resolve_in pn 0 in
        let assigns =
          List.concat_map
            (fun (s, kind) ->
              let arr = resolve_in s 0 in
              let ety = port_cty s 0 in
              let arr_tyid =
                match
                  ES.fold
                    (fun ((sn, sp), (dn, dp), ty) acc ->
                      if dn = s && dp = 0 && ty <> 0 then Some ty else acc)
                    g.eset None
                with
                | Some ty -> ty
                | None -> 0
              in
              let elem =
                if rank_of_type_id env_loop.tm arr_tyid > 1 && ety = C.Basic "sisal_array_t" then
                  C.Call ("sisal_array_get_row", [ arr; C.Id k ])
                else
                  C.Index
                    (C.Cast (C.Pointer (ety, []), C.Member (arr, "data")), C.Id k)
              in
              let base =
                [ C.Expr (C.BinOp (C.Assign, C.Id (slot s 0), elem)) ]
              in
              let at_used =
                SM.exists
                  (fun _ v -> v.val_def = s && v.def_port = 1)
                  (fst g.symtab)
              in
              match kind with
              | (`Arr | `Dv) when at_used ->
                  (* `at` index (port 1) = lower_bound[0] + k *)
                  let idx =
                    C.BinOp
                      ( C.Add,
                        C.Cast
                          ( C.Basic "int32_t",
                            C.Index (C.Member (arr, "lower_bound"), C.LitInt 0)
                          ),
                        C.Id k )
                  in
                  base @ [ C.Expr (C.BinOp (C.Assign, C.Id (slot s 1), idx)) ]
              | _ -> base)
            scatters
        in
        let arr_tyid =
          match
            ES.fold
              (fun ((sn, sp), (dn, dp), ty) acc ->
                if dn = pn && dp = 0 && ty <> 0 then Some ty else acc)
              g.eset None
          with
          | Some ty -> ty
          | None -> 0
        in
        let limit_expr =
          if rank_of_type_id env_loop.tm arr_tyid > 1 then
            C.Index (C.Member (parr, "dims"), C.LitInt 0)
          else
            C.Member (parr, "size")
        in
        pre @ before
        @ [
            C.For
              ( C.Decl (C.Basic "int32_t", k, Some (C.LitInt 0)),
                C.BinOp
                  ( C.Lt,
                    C.Id k,
                    C.Cast (C.Basic "int32_t", limit_expr) ),
                C.UnaryOp (C.PostInc, C.Id k),
                assigns @ inner' );
          ]
    | [], [] -> pre @ before @ inner'
    | _ :: _, _ :: _ ->
        pre @ inner' (* mixed range+scatter at one level: unsupported *)
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
        let env_gen_view =
          { env_loop with curr_gid = gen_gid; curr_gr = gen_gr }
        in
        let gen_internal n p =
          ES.fold
            (fun ((sn, sp), (dn, dp), _) acc ->
              if dn = n && dp = p then Some (sn, sp) else acc)
            gen_gr.eset None
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
            | Some (ign, igr) ->
                bind_gen_outputs ggid ign igr (gen_gid_of ggid ign) e
            | None -> e
          in
          let out_ports =
            ES.fold
              (fun (_, (dn, dp), _) acc ->
                if dn = 0 then IntSet.add dp acc else acc)
              g.eset IntSet.empty
          in
          IntSet.fold
            (fun p e ->
              match
                ES.fold
                  (fun ((sn, sp), (dn, dp), _) acc ->
                    if dn = 0 && dp = p then Some (sn, sp) else acc)
                  g.eset None
              with
              | Some (sn, sp) ->
                  let v =
                    get_expr
                      { e with curr_gid = ggid; curr_gr = g }
                      ggid sn sp `Out
                  in
                  {
                    e with
                    var_map =
                      FullPortMap.add
                        (parent_gid, comp_nid, p, `Out)
                        v e.var_map;
                  }
              | None -> e)
            out_ports e
        in
        let env_loop =
          bind_gen_outputs sub_gid gen_nid gen_gr gen_gid env_loop
        in
        (* (a2) materialise ALL generator-nest bound math (n-1, m-1, ...) UP FRONT.
           It is loop-invariant, so hoisting it before the alloc lets the result
           extent reference it even for nested expression bounds in a cross. *)
        let rec materialize_bounds g ggid e =
          let e = { e with curr_gid = ggid; curr_gr = g } in
          let stmts, e =
            List.fold_left
              (fun (acc, e) n ->
                match NM.find_opt n g.nmap with
                | Some (Simple (_, (RANGEGEN | DV_SCATTER | ASCATTER), _, _, _))
                  ->
                    (acc, e)
                | Some (Simple _ as node) ->
                    let s, e' = lower_node e g n node in
                    (acc @ s, e')
                | _ -> (acc, e))
              ([], e) (topo_sort g)
          in
          match find_subgraph g "GENERATOR" with
          | Some (ign, igr) ->
              let s2, e = materialize_bounds igr (gen_gid_of ggid ign) e in
              (stmts @ s2, e)
          | None -> (stmts, e)
        in
        let bound_stmts, env_loop =
          materialize_bounds gen_gr gen_gid env_loop
        in
        let env_loop =
          { env_loop with curr_gid = sub_gid; curr_gr = loop_gr }
        in
        (* (b) lower the BODY -> body_stmts + ALL outputs (one per return clause),
           sorted by destination port (forall output port = body output port). *)
        let body_stmts, body_outs =
          match find_subgraph loop_gr "BODY" with
          | Some (body_nid, body_gr) ->
              let body_gid = gen_gid_of sub_gid body_nid in
              let env_body =
                {
                  env_loop with
                  parent_env = Some env_loop;
                  curr_gid = body_gid;
                  curr_gr = body_gr;
                  parent_map =
                    IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map;
                }
              in
              let bstmts, e_body =
                lower_graph env_body loop_gr body_nid body_gr body_gid
              in
              let outs =
                ES.fold
                  (fun ((sn, sp), (dn, dp), t) acc ->
                    if dn = 0 then
                      (dp, get_expr e_body body_gid sn sp `Out, t) :: acc
                    else acc)
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
              ES.fold
                (fun ((sn, sp), (dn, dp), _) acc ->
                  if dn = n && dp = p then Some (sn, sp) else acc)
                g.eset None
            with
            | Some (sn, sp) -> get_expr view ggid sn sp `Out
            | None -> C.LitInt 0
          in
          let here =
            match
              List.find_opt
                (fun n ->
                  match NM.find_opt n g.nmap with
                  | Some
                      (Simple (_, (RANGEGEN | DV_SCATTER | ASCATTER), _, _, _))
                    ->
                      true
                  | _ -> false)
                (topo_sort g)
            with
            | Some n -> (
                match NM.find_opt n g.nmap with
                | Some (Simple (_, RANGEGEN, _, _, _)) ->
                    let lb = resolve n 0 and ub = resolve n 1 in
                    [
                      (C.BinOp (C.Add, C.BinOp (C.Sub, ub, lb), C.LitInt 1), lb);
                    ]
                | _ ->
                    [
                      ( C.Cast
                          ( C.Basic "int32_t",
                            C.Index (C.Member (resolve n 0, "dims"), C.LitInt 0)
                          ),
                        C.LitInt 1 );
                    ])
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
        (* DEPENDENT nest (see nest_is_dependent above): the preheader extent
           product is meaningless — a nested extent would read the axis slot
           before the loop has run.  Allocate FLAT instead: one extent = a
           total computed by a counting pre-nest (same loops, bare counter
           body) just before the real nest — rank 1, dims[0] = total. *)
        let gtot = Printf.sprintf "__gtot_%d" sub_gid in
        let extents =
          if dependent then [ (C.Id gtot, C.LitInt 1) ] else extents
        in
        let rank = max 1 (List.length extents) in
        let count =
          List.fold_left
            (fun acc (e, _) -> C.BinOp (C.Mul, acc, e))
            (C.LitInt 1) extents
        in
        let gctr = Printf.sprintf "__g_%d" sub_gid in
        (* which forall output ports are REDUCTIONS (vs gathers) *)
        let reduce_specs = forall_reduce_ports loop_gr in
        let reduce_op_of p =
          List.find_map
            (fun (op_port, opn, _) -> if op_port = p then Some opn else None)
            reduce_specs
        in
        (* RETURNS ports fed by FINALVALUE (`value of X`, keep-last) vs DV_GATHER. *)
        let final_specs = forall_finalvalue_ports loop_gr in
        let gather_specs = forall_gather_ports loop_gr in
        let is_final p = List.exists (fun (fp, _) -> fp = p) final_specs in
        let is_gather p = List.exists (fun (gp, _) -> gp = p) gather_specs in
        (* primary axis iterator (the Sisal index, for argmax/argmin) *)
        let primary_iter =
          match
            List.find_opt
              (fun n ->
                match NM.find_opt n gen_gr.nmap with
                | Some (Simple (_, RANGEGEN, _, _, _)) -> true
                | _ -> false)
              (topo_sort gen_gr)
          with
          | Some n ->
              Some
                (C.Id
                   (get_c_name env.proc_map env.gid_name_map gen_gid n 0 `Out
                      gen_gr))
          | None -> None
        in
        (* (c) per forall OUTPUT PORT: a gather (alloc + store) or a reduction
           (init + accumulate).  All share one loop + one gather counter. *)
        let per =
          List.map
            (fun (port, value, tid) ->
              let res_name =
                get_c_name env.proc_map env.gid_name_map gid nid port `Out gr
              in
              let res_v = C.Id res_name in
              let out_ty =
                c_type_of_if1_tyid tm tid
              in
              let cast =
                C.Call ("SISAL_CAST", [ C.Id (string_of_c_type out_ty); value ])
              in
              match reduce_op_of port with
              | Some ((R_argmax | R_argmin) as op) ->
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
                  let sentinel =
                    if op = R_argmax then C.UnaryOp (C.Negate, inf) else inf
                  in
                  let cmp = if op = R_argmax then C.Gt else C.Lt in
                  let idx =
                    match primary_iter with Some i -> i | None -> C.LitInt 0
                  in
                  let before =
                    [
                      C.Decl (out_ty, accn, Some sentinel);
                      C.Expr (C.BinOp (C.Assign, res_v, C.LitInt 0));
                    ]
                  in
                  let update =
                    C.If
                      ( C.BinOp (cmp, cast, accv),
                        [
                          C.Expr (C.BinOp (C.Assign, accv, cast));
                          C.Expr (C.BinOp (C.Assign, res_v, idx));
                        ],
                        [] )
                  in
                  ( before,
                    [ update ],
                    [],
                    (res_name, C.Basic "int32_t"),
                    (port, res_v) )
              | Some op when out_ty = C.Basic "sisal_array_t" ->
                  if op = R_catenate then
                    let update =
                      C.Expr
                        (C.BinOp
                           ( C.Assign,
                             res_v,
                             C.Call ("sisal_array_catenate", [ res_v; value ]) ))
                    in
                    ( [
                        C.Expr
                          (C.BinOp
                             (C.Assign, res_v, C.Call ("sisal_array_empty", [])));
                      ],
                      [ update ],
                      [],
                      (res_name, out_ty),
                      (port, res_v) )
                  else
                    let opcode =
                      match op with
                      | R_sum -> 0
                      | R_product -> 1
                      | R_greatest -> 2
                      | R_least -> 3
                      | _ -> assert false
                    in
                    let update =
                      C.Expr
                        (C.BinOp
                           ( C.Assign,
                             res_v,
                             C.Call
                               ( "sisal_array_ereduce",
                                 [ res_v; value; C.LitInt opcode ] ) ))
                    in
                    ( [
                        C.Expr
                          (C.BinOp
                             (C.Assign, res_v, C.Call ("sisal_array_empty", [])));
                      ],
                      [ update ],
                      [],
                      (res_name, out_ty),
                      (port, res_v) )
              | Some op ->
                  let inf =
                    match out_ty with
                    | C.Basic "double" -> C.Id "1e308"
                    | C.Basic "float" -> C.Id "3.4028235e+38f"
                    | _ -> C.Id "0x7fffffff"
                  in
                  let init_val =
                    match op with
                    | R_product -> C.LitInt 1
                    | R_least -> inf
                    | R_greatest -> C.UnaryOp (C.Negate, inf)
                    | R_sum -> C.LitInt 0
                    | R_argmax | R_argmin | R_catenate ->
                        assert false (* handled in the arm above *)
                  in
                  let update =
                    match op with
                    | R_product ->
                        C.Expr
                          (C.BinOp
                             (C.Assign, res_v, C.BinOp (C.Mul, res_v, cast)))
                    | R_least ->
                        C.If
                          ( C.BinOp (C.Lt, cast, res_v),
                            [ C.Expr (C.BinOp (C.Assign, res_v, cast)) ],
                            [] )
                    | R_greatest ->
                        C.If
                          ( C.BinOp (C.Gt, cast, res_v),
                            [ C.Expr (C.BinOp (C.Assign, res_v, cast)) ],
                            [] )
                    | R_sum ->
                        let o =
                          if out_ty = C.Basic "bool" then C.LogOr else C.Add
                        in
                        C.Expr
                          (C.BinOp (C.Assign, res_v, C.BinOp (o, res_v, cast)))
                    | R_argmax | R_argmin | R_catenate ->
                        assert false (* handled in the arm above *)
                  in
                  ( [ C.Expr (C.BinOp (C.Assign, res_v, init_val)) ],
                    [ update ],
                    [],
                    (res_name, out_ty),
                    (port, res_v) )
              | None when is_final port ->
                  (* FINALVALUE: `value of X` with no reduction operator returns the
                     LAST iteration's value.  Overwrite res_v with the body value each
                     iteration; after the loop it holds the final value.  No alloc, no
                     gather counter, no box-then-flatten — works for scalar AND array
                     bodies (out_ty carries the body value's type). *)
                  ( [],
                    [ C.Expr (C.BinOp (C.Assign, res_v, cast)) ],
                    [],
                    (res_name, out_ty),
                    (port, res_v) )
              | None ->
                  (* Not a reduction and not a FINALVALUE — it MUST be a genuine
                     DV_GATHER.  Fail loudly on anything else rather than silently
                     miscompiling an unhandled RETURNS kind as a gather. *)
                  if not (is_gather port) then
                    failwith
                      (Printf.sprintf
                         "lower_forall: RETURNS port %d is neither REDUCE, \
                          FINALVALUE nor DV_GATHER -- unhandled forall returns \
                          kind"
                         port);
                  (* DV_SCATTER_AT: store slot comes from the PLACEMENT values
                     (node ports 3+), allocation from the DECLARED extents
                     (DV_MAKE_DOPE ports 2+) -- NOT from the generator ranges
                     or the flat counter.  Placements are per-iteration BODY
                     values; extents arrive on the forall boundary
                     (loop-invariant, preheader-safe). *)
                  let scatter =
                    match find_subgraph loop_gr "RETURNS" with
                    | None -> None
                    | Some (rn_nid, r_gr) -> (
                        let gnid =
                          ES.fold
                            (fun ((sn, _), (dn, dp), _) a ->
                              if dn = 0 && dp = port then Some sn else a)
                            r_gr.eset None
                        in
                        match gnid with
                        | Some g -> (
                            match NM.find_opt g r_gr.nmap with
                            | Some (Simple (_, DV_SCATTER_AT, _, _, _)) ->
                                (* RETURNS boundary port -> C expr, via the
                                   forall-level edge into the RETURNS compound:
                                   src 0 = forall boundary (extent), src other
                                   = BODY compound (placement). *)
                                let rb_expr rp =
                                  match
                                    ES.fold
                                      (fun ((sn2, sp2), (dn2, dp2), _) a ->
                                        if dn2 = rn_nid && dp2 = rp then
                                          Some (sn2, sp2)
                                        else a)
                                      loop_gr.eset None
                                  with
                                  | Some (0, q) ->
                                      get_expr env_loop sub_gid 0 q `Out
                                  | Some (_, dp) -> (
                                      match
                                        List.find_opt
                                          (fun (p, _, _) -> p = dp)
                                          body_outs
                                      with
                                      | Some (_, e, _) -> e
                                      | None ->
                                          failwith
                                            "forall scatter: placement has no \
                                             lowered body output")
                                  | None ->
                                      failwith
                                        "forall scatter: RETURNS input not \
                                         wired"
                                in
                                let ports_from node lo =
                                  ES.fold
                                    (fun ((sn, sp), (dn, dp), _) acc ->
                                      if dn = node && dp >= lo && sn = 0 then
                                        (dp, sp) :: acc
                                      else acc)
                                    r_gr.eset []
                                  |> List.sort compare
                                in
                                let plcs =
                                  List.map
                                    (fun (_, rp) -> rb_expr rp)
                                    (ports_from g 3)
                                in
                                let exts =
                                  match
                                    ES.fold
                                      (fun ((sn, _), (dn, dp), _) a ->
                                        if dn = g && dp = 2 then Some sn else a)
                                      r_gr.eset None
                                  with
                                  | Some m ->
                                      List.map
                                        (fun (_, rp) -> rb_expr rp)
                                        (ports_from m 2)
                                  | None -> []
                                in
                                Some (plcs, exts)
                            | _ -> None)
                        | None -> None)
                  in
                  match scatter with
                  | Some (plcs, exts)
                    when out_ty = C.Basic "sisal_array_t" ->
                      (* ARRAY-valued element: the element's dims become the
                         TAIL of the shape at its slot.  Element byte size and
                         rank are runtime values off the element's dope, so
                         allocation is lazy (first store) -- reuse the
                         for-initial helper: one whole-element memcpy per
                         iteration at slot = placement - 1.  Single leading
                         coordinate only for now (a rank>1 placement of a tile
                         needs strided copies). *)
                      (match (plcs, exts) with
                      | [ p ], [ e ] ->
                          let before =
                            [
                              C.Expr
                                (C.BinOp
                                   ( C.Assign,
                                     res_v,
                                     C.Call ("sisal_array_empty", []) ));
                            ]
                          in
                          let store =
                            [
                              C.Expr
                                (C.BinOp
                                   ( C.Assign,
                                     res_v,
                                     C.Call
                                       ( "sisal_array_shaped_store",
                                         [
                                           res_v;
                                           value;
                                           C.Cast (C.Basic "int64_t", e);
                                           C.Cast
                                             ( C.Basic "int64_t",
                                               C.BinOp (C.Sub, p, C.LitInt 1)
                                             );
                                         ] ) ));
                            ]
                          in
                          ( before,
                            store,
                            [],
                            (res_name, C.Basic "sisal_array_t"),
                            (port, res_v) )
                      | _ ->
                          failwith
                            "forall scatter of array elements: single leading \
                             coordinate only (tile placement not lowered yet)")
                  | Some (plcs, exts) ->
                      if plcs = [] || List.length plcs <> List.length exts then
                        failwith
                          "forall scatter: placement/extent arity mismatch";
                      let k = List.length exts in
                      let total =
                        List.fold_left
                          (fun a e -> C.BinOp (C.Mul, a, e))
                          (List.hd exts) (List.tl exts)
                      in
                      let alloc =
                        C.Expr
                          (C.BinOp
                             ( C.Assign,
                               res_v,
                               alloc_array_call (C.LitInt k) (C.LitInt tid)
                                 (C.Cast (C.Basic "uint64_t", total))
                                 out_ty ))
                        :: List.concat
                             (List.mapi
                                (fun j e ->
                                  [
                                    C.Expr
                                      (C.BinOp
                                         ( C.Assign,
                                           C.Index
                                             ( C.Member (res_v, "dims"),
                                               C.LitInt j ),
                                           e ));
                                    C.Expr
                                      (C.BinOp
                                         ( C.Assign,
                                           C.Index
                                             ( C.Member (res_v, "lower_bound"),
                                               C.LitInt j ),
                                           C.LitInt 1 ));
                                  ])
                                exts)
                      in
                      (* row-major slot from 1-based placements (Horner):
                         slot = (...((p0-1)*e1 + (p1-1))*e2 + ...) *)
                      let slot =
                        match (plcs, exts) with
                        | p0 :: ptl, _ :: etl ->
                            List.fold_left2
                              (fun acc p e ->
                                C.BinOp
                                  ( C.Add,
                                    C.BinOp (C.Mul, acc, e),
                                    C.BinOp (C.Sub, p, C.LitInt 1) ))
                              (C.BinOp (C.Sub, p0, C.LitInt 1))
                              ptl etl
                        | _ -> assert false
                      in
                      let store =
                        [
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 C.Index
                                   ( C.Cast
                                       ( C.Pointer (out_ty, []),
                                         C.Member (res_v, "data") ),
                                     C.Cast (C.Basic "int64_t", slot) ),
                                 cast ));
                        ]
                      in
                      ( alloc,
                        store,
                        [],
                        (res_name, C.Basic "sisal_array_t"),
                        (port, res_v) )
                  | None ->
                  let alloc =
                    C.Expr
                      (C.BinOp
                         ( C.Assign,
                           res_v,
                           alloc_array_call (C.LitInt rank) (C.LitInt tid)
                             (C.Cast (C.Basic "uint64_t", count))
                             out_ty ))
                    :: List.concat
                         (List.mapi
                            (fun k (e, lb) ->
                              [
                                C.Expr
                                  (C.BinOp
                                     ( C.Assign,
                                       C.Index
                                         (C.Member (res_v, "dims"), C.LitInt k),
                                       e ));
                                C.Expr
                                  (C.BinOp
                                     ( C.Assign,
                                       C.Index
                                         ( C.Member (res_v, "lower_bound"),
                                           C.LitInt k ),
                                       lb ));
                              ])
                            extents)
                  in
                  let store =
                    [
                      C.Expr
                        (C.BinOp
                           ( C.Assign,
                             C.Index
                               ( C.Cast
                                   ( C.Pointer (out_ty, []),
                                     C.Member (res_v, "data") ),
                                 C.Id gctr ),
                             cast ));
                    ]
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
                      let e0 = C.Id ("__e0_" ^ res_name)
                      and fl = C.Id ("__flat_" ^ res_name) in
                      let esz = C.Call ("sisal_esz", [ e0 ]) in
                      let ecount = C.Member (e0, "size") in
                      let bytes = C.BinOp (C.Mul, ecount, esz) in
                      let boxed i =
                        C.Index
                          ( C.Cast
                              (C.Pointer (sat, []), C.Member (res_v, "data")),
                            i )
                      in
                      let decl_e0 =
                        C.Decl
                          (sat, "__e0_" ^ res_name, Some (boxed (C.LitInt 0)))
                      in
                      let decl_fl =
                        C.Decl
                          ( sat,
                            "__flat_" ^ res_name,
                            Some
                              (C.Call
                                 ( "sisal_array_alloc_sized",
                                   [
                                     C.BinOp
                                       ( C.Add,
                                         C.LitInt rank,
                                         C.Member (e0, "rank") );
                                     C.Member (e0, "type_id");
                                     C.Cast
                                       ( C.Basic "uint64_t",
                                         C.BinOp
                                           ( C.Mul,
                                             C.Cast (C.Basic "uint64_t", count),
                                             ecount ) );
                                     esz;
                                   ] )) )
                      in
                      let outer_dims =
                        List.concat
                          (List.mapi
                             (fun k (e, lb) ->
                               [
                                 C.Expr
                                   (C.BinOp
                                      ( C.Assign,
                                        C.Index
                                          (C.Member (fl, "dims"), C.LitInt k),
                                        e ));
                                 C.Expr
                                   (C.BinOp
                                      ( C.Assign,
                                        C.Index
                                          ( C.Member (fl, "lower_bound"),
                                            C.LitInt k ),
                                        lb ));
                               ])
                             extents)
                      in
                      let kk = "__fk_" ^ res_name in
                      let inner_dims =
                        C.For
                          ( C.Decl (C.Basic "int32_t", kk, Some (C.LitInt 0)),
                            C.BinOp (C.Lt, C.Id kk, C.Member (e0, "rank")),
                            C.UnaryOp (C.PostInc, C.Id kk),
                            [
                              C.Expr
                                (C.BinOp
                                   ( C.Assign,
                                     C.Index
                                       ( C.Member (fl, "dims"),
                                         C.BinOp (C.Add, C.LitInt rank, C.Id kk)
                                       ),
                                     C.Index (C.Member (e0, "dims"), C.Id kk) ));
                              C.Expr
                                (C.BinOp
                                   ( C.Assign,
                                     C.Index
                                       ( C.Member (fl, "lower_bound"),
                                         C.BinOp (C.Add, C.LitInt rank, C.Id kk)
                                       ),
                                     C.Index
                                       (C.Member (e0, "lower_bound"), C.Id kk)
                                   ));
                            ] )
                      in
                      let ii = "__fi_" ^ res_name in
                      let copy =
                        C.For
                          ( C.Decl (C.Basic "int32_t", ii, Some (C.LitInt 0)),
                            C.BinOp
                              (C.Lt, C.Id ii, C.Cast (C.Basic "int32_t", count)),
                            C.UnaryOp (C.PostInc, C.Id ii),
                            [
                              C.Expr
                                (C.Call
                                   ( "memcpy",
                                     [
                                       C.BinOp
                                         ( C.Add,
                                           C.Cast
                                             ( C.Pointer (C.Basic "char", []),
                                               C.Member (fl, "data") ),
                                           C.BinOp
                                             ( C.Mul,
                                               C.Cast
                                                 (C.Basic "uint64_t", C.Id ii),
                                               bytes ) );
                                       C.Member (boxed (C.Id ii), "data");
                                       bytes;
                                     ] ));
                            ] )
                      in
                      [ decl_e0; decl_fl ] @ outer_dims
                      @ [
                          inner_dims;
                          copy;
                          C.Expr (C.BinOp (C.Assign, res_v, fl));
                        ]
                  in
                  (alloc, store, after, (res_name, sat), (port, res_v)))
            (* Only the CLAUSE outputs: the BODY also exports scatter
               placements (ports past the RETURNS output count), which are
               operands of the scatter stores, not forall outputs. *)
            (let n_forall_outs =
               match find_subgraph loop_gr "RETURNS" with
               | Some (_, rg) -> List.length (get_boundary_outputs rg)
               | None -> List.length body_outs
             in
             List.filter (fun (p, _, _) -> p < n_forall_outs) body_outs)
        in
        let per_filtered =
          List.map
            (fun (before, updates, after, ty, (port, res_v)) ->
              let filter_opt = forall_reduce_filter_of loop_gr port in
              match filter_opt with
              | Some filter_bport ->
                  let filter_expr =
                    match
                      List.find_opt
                        (fun (dp, _, _) -> dp = filter_bport)
                        body_outs
                    with
                    | Some (_, expr, _) -> expr
                    | None -> C.LitInt 1
                  in
                  (before, [ C.If (filter_expr, updates, []) ], after, ty, (port, res_v))
              | None -> (before, updates, after, ty, (port, res_v)))
            per
        in
        let befores = List.concat_map (fun (b, _, _, _, _) -> b) per_filtered in
        let inners = List.concat_map (fun (_, i, _, _, _) -> i) per_filtered in
        let afters = List.concat_map (fun (_, _, a, _, _) -> a) per_filtered in
        let decls = List.map (fun (_, _, _, d, _) -> d) per_filtered in
        let binds = List.map (fun (_, _, _, _, b) -> b) per_filtered in
        let any_gather =
          List.exists
            (fun (p, _, _) -> reduce_op_of p = None && not (is_final p))
            body_outs
        in
        let before =
          befores
          @
          if any_gather then
            [ C.Decl (C.Basic "int32_t", gctr, Some (C.LitInt 0)) ]
          else []
        in
        let inner =
          body_stmts @ inners
          @
          if any_gather then [ C.Expr (C.UnaryOp (C.PostInc, C.Id gctr)) ]
          else []
        in
        (* dependent nest: run the SAME loops once with a bare counter body
           to learn the flat element count before the gather allocations
           (which sit in `before`, ahead of the real nest) read __gtot. *)
        let count_nest =
          if dependent && any_gather then
            C.Decl (C.Basic "int64_t", gtot, Some (C.LitInt 0))
            :: lower_gen gen_gr gen_gid
                 [ C.Expr (C.UnaryOp (C.PostInc, C.Id gtot)) ]
          else []
        in
        ( bound_stmts @ count_nest
          @ lower_gen ~before gen_gr gen_gid inner
          @ afters,
          decls,
          binds )
  in
  (* Declare each forall output in the PARENT scope (gather -> sisal_array_t,
     reduction -> scalar), and bind it in var_map so the caller resolves it. *)
  let res_decls =
    List.filter_map
      (fun (n, t) ->
        if StringSet.mem n env.seen_decls then None
        else
          let iv =
            if t = C.Basic "sisal_array_t" then C.Id "{0}" else C.LitInt 0
          in
          Some (C.Decl (t, n, Some iv)))
      out_decls
  in
  let env_out =
    List.fold_left
      (fun e (port, res_v) ->
        {
          e with
          var_map = FullPortMap.add (gid, nid, port, `Out) res_v e.var_map;
        })
      {
        env with
        curr_gid = gid;
        curr_gr = gr;
        seen_decls =
          List.fold_left
            (fun s (n, _) -> StringSet.add n s)
            env.seen_decls out_decls;
      }
      out_binds
  in
  (res_decls @ [ C.Compound (sym_decls @ relay_stmts @ loop_stmts) ], env_out)

(** [lower_for_initial env gr gid nid loop_gr sub_gid pr] — a LoopA/LoopB
    (for-initial) compound to preheader + while.  Loop-carried state lives in
    MERGE (phi) variables: seeded from INIT outputs before the loop, fed back
    by snapshot copies at the bottom of the body (bodycaps).  INIT lowers
    flat into the loop scope; TEST lowers twice (preheader cond + in-loop
    re-evaluation); RETURNS gathers/scatters are realized as
    alloc-before-loop + per-iteration store (declared extents when shaped,
    TEST bound-seed as the bare fallback), and the RETURNS graph itself is
    lowered after the loop with gather ports re-bound to the filled arrays. *)
and lower_for_initial env gr gid nid loop_gr sub_gid pr =
  let init_nid, init_gr =
    match find_subgraph loop_gr "INIT" with
    | Some x -> x
    | _ -> failwith "no INIT"
  in
  let augment_loop_symtab () =
    let test_nid, test_gr =
      match find_subgraph loop_gr "TEST" with | Some x -> x | _ -> failwith "no TEST"
    in
    let body_nid, body_gr =
      match find_subgraph loop_gr "BODY" with | Some x -> x | _ -> failwith "no BODY"
    in
    let ret_nid, ret_gr =
      match find_subgraph loop_gr "RETURNS" with | Some x -> x | _ -> failwith "no RET"
    in
    let get_subgraph_by_nid dn =
      if dn = test_nid then Some test_gr
      else if dn = body_nid then Some body_gr
      else if dn = ret_nid then Some ret_gr
      else None
    in
    let merge_nodes =
      NM.fold
        (fun nid node acc ->
          match node with
          | Simple (_, MERGE, _, _, _) -> IntSet.add nid acc
          | _ -> acc)
        loop_gr.nmap IntSet.empty
    in
    let merged_init_ports =
      ES.fold
        (fun ((sn, sp), (dn, dp), _) acc ->
          if sn = init_nid && IntSet.mem dn merge_nodes && dp = 1 then
            IntSet.add sp acc
          else acc)
        loop_gr.eset IntSet.empty
    in
    let init_outputs =
      ES.fold
        (fun ((sn, sp), _, _) acc ->
          if sn = init_nid then IntSet.add sp acc else acc)
        loop_gr.eset IntSet.empty
    in
    let non_merged_ports = IntSet.diff init_outputs merged_init_ports in
    if IntSet.is_empty non_merged_ports then (loop_gr, IntSet.empty)
    else
      let cs_loop, ps_loop = loop_gr.symtab in
      let cs_loop' =
        IntSet.fold
          (fun sp cs_acc ->
            match
              ES.fold
                (fun ((sn, sp2), (dn, dp), _) a ->
                  if sn = init_nid && sp2 = sp && dn <> 0 then Some (dn, dp) else a)
                loop_gr.eset None
            with
            | Some (dn, dp) -> (
                match get_subgraph_by_nid dn with
                | Some target_gr -> (
                    let cs_t, _ = target_gr.symtab in
                    match
                      SM.fold
                        (fun v name_entry a ->
                          if name_entry.val_def = 0 && name_entry.def_port = dp then Some (v, name_entry.val_ty) else a)
                        cs_t None
                    with
                    | Some (v, val_ty) ->
                        SM.add v
                          {
                            val_name = v;
                            val_ty = val_ty;
                            val_def = init_nid;
                            def_port = sp;
                          }
                          cs_acc
                    | None -> cs_acc)
                | None -> cs_acc)
            | None -> cs_acc)
          non_merged_ports cs_loop
      in
      ({ loop_gr with symtab = (cs_loop', ps_loop) }, non_merged_ports)
  in
  let loop_gr, non_merged_ports = augment_loop_symtab () in
  let env_init_base =
    {
      env with
      parent_env = Some env;
      compound_nid_in_parent = nid;
      curr_gid = sub_gid;
      curr_gr = loop_gr;
    }
  in
  let env_init_base = scan_fanout loop_gr sub_gid env_init_base in
  let node =
    match NM.find_opt nid gr.nmap with Some n -> n | _ -> failwith "no node"
  in
  let decl_stmts, env_init_base =
    declare_outputs env_init_base gr gid nid node
  in
  let loop_in_stmts, env_loop =
    init_boundary_ports env_init_base gr nid loop_gr sub_gid
  in
  (* Declare the LoopB scope's own local symtab entries at the top of the for-initial
     scope (the subgraphs INIT/BODY/TEST/RETURNS already get this via lower_graph's
     call to pre_declare_graph_locals; the loop_gr level did not until now). *)
  let loop_local_decls, env_loop =
    pre_declare_graph_locals env_loop loop_gr sub_gid
  in
  (* The loop-carried state lives in the MERGE (phi) nodes of loop_gr, which are NOT
     symtab entries (the loop_gr local symtab only holds the loop input/result). Emit one
     declarator per MERGE at the top of the for-initial scope, and bind it into var_map /
     type_table / seen_decls at the MERGE's output port so TEST/BODY/RETURNS consumers
     resolve to this carry variable. Each MERGE corresponds to one INIT output. *)
  let loop_tm = get_typemap_tm loop_gr in
  let merge_decls, env_loop =
    NM.fold
      (fun mnid mnode (acc, e) ->
        match mnode with
        | Simple (_, MERGE, _, _, mpr) ->
            let raw =
              List.find_map (function Name n -> Some n | _ -> None) mpr
              |> Option.value ~default:(Printf.sprintf "merge_%d" mnid)
            in
            let vname =
              Printf.sprintf "v_%s_n__%d_%s"
                (scope_of e.gid_name_map sub_gid)
                mnid (sanitize raw)
            in
            if StringSet.mem vname e.seen_decls then (acc, e)
            else
              let ty =
                match
                  ES.fold
                    (fun ((sn, sp), _, t) a ->
                      if sn = mnid && sp = 0 && t <> 0 then Some t else a)
                    loop_gr.eset None
                with
                | Some t -> (
                    try c_type_of_if1_ty loop_tm (TM.find t loop_tm)
                    with _ -> C.Basic "int32_t")
                | None -> C.Basic "int32_t"
              in
              let init_val =
                if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}")
                else Some (C.LitInt 0)
              in
              let e' =
                {
                  e with
                  seen_decls = StringSet.add vname e.seen_decls;
                  var_map =
                    FullPortMap.add (sub_gid, mnid, 0, `Out) (C.Id vname)
                      e.var_map;
                  type_table =
                    FullPortMap.add (sub_gid, mnid, 0, `Out) ty e.type_table;
                }
              in
              (acc @ [ C.Decl (ty, vname, init_val) ], e')
        | _ -> (acc, e))
      loop_gr.nmap ([], env_loop)
  in
  (* Helper: find C expression and type for subgraph boundary output port op after lowering *)
  let get_sub_out_expr_and_ty sub_gid_x nid_x sub_gr_x e_sub op =
    match FullPortMap.find_opt (sub_gid_x, 0, op, `In) e_sub.var_map with
    | Some expr ->
        let ty =
          match FullPortMap.find_opt (sub_gid_x, 0, op, `In) e_sub.type_table with
          | Some t -> t
          | None -> C.Basic "int32_t"
        in
        Some (expr, ty)
    | None -> (
        match
          ES.fold
            (fun ((sn, sp), (dn, dp), _) a ->
              if dn = 0 && dp = op then Some (sn, sp) else a)
            sub_gr_x.eset None
        with
        | Some (sn, sp) -> (
            match
              FullPortMap.find_opt (sub_gid_x, sn, sp, `Out) e_sub.var_map
            with
            | Some expr ->
                let ty =
                  match
                    FullPortMap.find_opt (sub_gid_x, sn, sp, `Out) e_sub.type_table
                  with
                  | Some t -> t
                  | None -> C.Basic "int32_t"
                in
                Some (expr, ty)
            | None -> None)
        | None -> (
            (* Try looking up via compound output edge in loop_gr *)
            match
              ES.fold
                (fun ((sn, sp), (dn, dp), _) a ->
                  if sn = nid_x && sp = op then Some (dn, dp) else a)
                loop_gr.eset None
            with
            | Some _ -> None
            | None -> None))
  in
  let get_sub_out_expr sub_gid_x nid_x sub_gr_x e_sub op =
    match get_sub_out_expr_and_ty sub_gid_x nid_x sub_gr_x e_sub op with
    | Some (expr, _) -> Some expr
    | None -> None
  in
  (* Bug 5: helper to copy subgraph outputs to carry-slot var_map entries.
     For each edge (subgraph_nid:op) → (0:cp) in loop_gr, find the C expression
     for subgraph output op and assign it to var_map[(sub_gid, 0, cp, Out)]. *)
  let update_carry_slots sub_nid sub_gid_x sub_gr_x e_sub e_outer =
    ES.fold
      (fun ((sn, sp), (dn, dp), _) (acc_stmts, e) ->
        if sn = sub_nid && dn = 0 then
          match get_sub_out_expr sub_gid_x sub_nid sub_gr_x e_sub sp with
          | Some src_expr ->
              let stmts, e' = assign_with_cast e sub_gid 0 dp `Out src_expr in
              (acc_stmts @ stmts, e')
          | None -> (acc_stmts, e)
        else (acc_stmts, e))
      loop_gr.eset ([], e_outer)
  in
  (* Copy non-merged boundary outputs of INIT into parent-level variables *)
  let copy_non_merged_outputs sub_nid sub_gid_x sub_gr_x e_sub e_outer =
    IntSet.fold
      (fun sp (acc_stmts, e) ->
        match get_sub_out_expr sub_gid_x sub_nid sub_gr_x e_sub sp with
        | Some src_expr ->
            let parent_var = get_expr e sub_gid sub_nid sp `Out in
            let assign = C.Expr (C.BinOp (C.Assign, parent_var, src_expr)) in
            (acc_stmts @ [ assign ], e)
        | None -> (acc_stmts, e))
      non_merged_ports ([], e_outer)
  in
  let init_gid =
    try GidMap.find (sub_gid, init_nid) env.gid_table with _ -> -1
  in
  let env_init =
    {
      env_loop with
      parent_env = Some env_loop;
      curr_gid = init_gid;
      curr_gr = init_gr;
      parent_map = IntMap.add init_gid (sub_gid, init_nid) env_loop.parent_map;
    }
  in
  let init_stmts, e_init =
    lower_graph env_init loop_gr init_nid init_gr init_gid
  in
  let env_loop =
    {
      env_loop with
      var_map = e_init.var_map;
      type_table = e_init.type_table;
      seen_decls = e_init.seen_decls;
    }
  in
  (* Bug 5: after INIT, initialise carry-slot C variables from INIT outputs *)
  let carry_init_stmts, env_loop =
    update_carry_slots init_nid init_gid init_gr e_init env_loop
  in
  let copy_non_merged_stmts, env_loop =
    copy_non_merged_outputs init_nid init_gid init_gr e_init env_loop
  in
  (* Front-edge seeding: copy each MERGE phi's initial value (input port 1, sourced from an
     INIT boundary output) into the MERGE variable BEFORE the loop runs. This is the entry
     counterpart to the backedge copies; together they replace the MERGE_first select.
     INIT statements are emitted flat in the LoopB scope, so the INIT-internal variables are
     in scope here. *)
  let merge_init_seeds =
    NM.fold
      (fun mnid mnode acc ->
        match mnode with
        | Simple (_, MERGE, _, _, _) -> (
            match
              ES.fold
                (fun ((sn, sp), (dn, dp), _) a ->
                  if dn = mnid && dp = 1 then Some (sn, sp) else a)
                loop_gr.eset None
            with
            | Some (sn, sp) when sn = init_nid -> (
                match get_sub_out_expr init_gid init_nid init_gr e_init sp with
                | Some rhs ->
                    let lhs = get_expr env_loop sub_gid mnid 0 `Out in
                    acc @ [ C.Expr (C.BinOp (C.Assign, lhs, rhs)) ]
                | None -> acc)
            | _ -> acc)
        | _ -> acc)
      loop_gr.nmap []
  in
  let test_nid, test_gr =
    match find_subgraph loop_gr "TEST" with
    | Some x -> x
    | _ -> failwith "no TEST"
  in
  let test_gid =
    try GidMap.find (sub_gid, test_nid) env.gid_table with _ -> -1
  in
  (* Run TEST once (outside while) to get cond expression and pre-declare its vars *)
  let env_test1 =
    {
      env_loop with
      parent_env = Some env_loop;
      curr_gid = test_gid;
      curr_gr = test_gr;
      parent_map = IntMap.add test_gid (sub_gid, test_nid) env_loop.parent_map;
    }
  in
  let test_stmts1, e_test1 =
    lower_graph env_test1 loop_gr test_nid test_gr test_gid
  in
  let cond =
    match
      ES.fold
        (fun (src, dst, _) acc -> if dst = (0, 0) then Some src else acc)
        test_gr.eset None
    with
    | Some (sn, sp) -> get_expr e_test1 test_gid sn sp `Out
    | None -> C.LitInt 0
  in
  let env_loop =
    {
      env_loop with
      var_map = e_test1.var_map;
      type_table = e_test1.type_table;
      seen_decls = e_test1.seen_decls;
    }
  in
  let body_nid, body_gr =
    match find_subgraph loop_gr "BODY" with
    | Some x -> x
    | _ -> failwith "no BODY"
  in
  let body_gid =
    try GidMap.find (sub_gid, body_nid) env.gid_table with _ -> -1
  in
  let env_body =
    {
      env_loop with
      parent_env = Some env_loop;
      curr_gid = body_gid;
      curr_gr = body_gr;
      parent_map = IntMap.add body_gid (sub_gid, body_nid) env_loop.parent_map;
    }
  in
  let body_stmts, e_body =
    lower_graph env_body loop_gr body_nid body_gr body_gid
  in
  let env_loop =
    {
      env_loop with
      var_map = e_body.var_map;
      type_table = e_body.type_table;
      seen_decls = e_body.seen_decls;
    }
  in
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
    ES.fold
      (fun ((sn, sp), (dn, dp), _) (decls, assigns, e) ->
        (* Capture every body boundary output (dn = 0), including pass-throughs sourced
         from the body's boundary input (sn = 0). Capturing pass-throughs too guarantees
         that every MERGE backedge source is a snapshot, never a live MERGE variable. *)
        if dn = 0 then
          match Hashtbl.find_opt memo (sn, sp) with
          | Some cap_id ->
              Printf.eprintf
                "warning: lower_for_initial: BODY boundary out port %d \
                 duplicates source (%d,%d) at gid=%d; reusing memoized capture\n"
                dp sn sp sub_gid;
              ( decls,
                assigns,
                {
                  e with
                  var_map =
                    FullPortMap.add
                      (sub_gid, body_nid, dp, `Out)
                      cap_id e.var_map;
                } )
          | None -> (
              match
                FullPortMap.find_opt (body_gid, sn, sp, `Out) e_body.var_map
              with
              | Some src_expr ->
                  let cap_name =
                    Printf.sprintf "v_%s_bodycap_n%d_p%d"
                      (scope_of env.gid_name_map sub_gid)
                      sn sp
                  in
                  let cap_id = C.Id cap_name in
                  let ty = get_final_ty e body_gid sn sp `Out in
                  let init_val =
                    if ty = C.Basic "sisal_array_t" then Some (C.Id "{0}")
                    else Some (C.LitInt 0)
                  in
                  Hashtbl.add memo (sn, sp) cap_id;
                  ( decls @ [ C.Decl (ty, cap_name, init_val) ],
                    assigns @ [ C.Expr (C.BinOp (C.Assign, cap_id, src_expr)) ],
                    {
                      e with
                      seen_decls = StringSet.add cap_name e.seen_decls;
                      var_map =
                        FullPortMap.add
                          (sub_gid, body_nid, dp, `Out)
                          cap_id e.var_map;
                      type_table =
                        FullPortMap.add
                          (sub_gid, body_nid, dp, `Out)
                          ty e.type_table;
                    } )
              | None -> (decls, assigns, e))
        else (decls, assigns, e))
      body_gr.eset ([], [], env_loop)
  in
  (* ---- for-initial gather (`returns array of X`): realize each DV_GATHER RETURNS
     port as alloc-before-loop + per-iteration store.  Size is read off the loop, not
     taken from the IF1: upper = the TEST compare's bound operand (cond's RHS), lower =
     the induction seed (cond's LHS evaluated in the preheader, where the carry still
     holds its INIT value), size = upper-lower+1 for `<=`.  Both operands are already
     lowered nodes (in `cond`); we bind them to fresh preheader names and let the C++
     compiler CSE the duplicates -- no symbol-name guessing. *)
  let g_ret_nid, g_ret_gr =
    match find_subgraph loop_gr "RETURNS" with
    | Some x -> x
    | _ -> failwith "no RET"
  in
  let gather_pre, gather_store, gather_binds =
    List.fold_left
      (fun (pre, store, binds) (ret_out_port, ret_bin_port) ->
        (* BODY output port feeding the RETURNS boundary input the gather reads *)
        let body_port =
          ES.fold
            (fun ((s, sp), (d, p), _) a ->
              if d = g_ret_nid && p = ret_bin_port && s = body_nid then Some sp
              else a)
            loop_gr.eset None
        in
        match body_port with
        | None -> (pre, store, binds)
        | Some bp -> (
            match
              FullPortMap.find_opt
                (sub_gid, body_nid, bp, `Out)
                env_loop.var_map
            with
            | None -> (pre, store, binds)
            | Some body_val ->
                let tid =
                  ES.fold
                    (fun ((s, sp), (_, _), ty) a ->
                      if s = body_nid && sp = bp then Some ty else a)
                    loop_gr.eset None
                  |> function
                  | Some t -> t
                  | None -> 4
                in
                let elem_ty = c_type_of_if1_tyid env.tm tid in
                let res_name =
                  get_c_name env.proc_map env.gid_name_map gid nid ret_out_port
                    `Out gr
                in
                let res_v = C.Id res_name in
                let ctr = Printf.sprintf "__gctr_%d_%d" sub_gid ret_out_port in
                let is_arr_elem = elem_ty = C.Basic "sisal_array_t" in
                let gnid =
                  ES.fold
                    (fun ((sn, _), (dn, dp), _) a ->
                      if dn = 0 && dp = ret_out_port then Some sn else a)
                    g_ret_gr.eset None
                in
                (* DV_SCATTER_AT: the per-iteration destination coordinate is on
                   node port 3, a RETURNS boundary input wired from a BODY
                   output -- it resolves to the body-capture var, which is
                   assigned each iteration BEFORE the gather store runs.
                   Placement is 1-based (Sisal indexing); the store subtracts
                   the lower bound. *)
                let place_opt =
                  match gnid with
                  | Some g -> (
                      match NM.find_opt g g_ret_gr.nmap with
                      | Some (Simple (_, DV_SCATTER_AT, _, _, _)) ->
                          if
                            ES.exists
                              (fun ((_, _), (dn, dp), _) -> dn = g && dp = 4)
                              g_ret_gr.eset
                          then
                            failwith
                              "scatter: multi-coordinate placement (rank > 1) \
                               not lowered yet";
                          let pb =
                            match
                              ES.fold
                                (fun ((sn, sp), (dn, dp), _) a ->
                                  if dn = g && dp = 3 && sn = 0 then Some sp
                                  else a)
                                g_ret_gr.eset None
                            with
                            | Some pb -> pb
                            | None ->
                                failwith
                                  "scatter: missing placement on port 3"
                          in
                          let sn2, sp2 =
                            match
                              ES.fold
                                (fun ((sn2, sp2), (dn2, dp2), _) a ->
                                  if dn2 = g_ret_nid && dp2 = pb then
                                    Some (sn2, sp2)
                                  else a)
                                loop_gr.eset None
                            with
                            | Some x -> x
                            | None ->
                                failwith
                                  "scatter: placement not wired into RETURNS"
                          in
                          Some (get_expr env_loop sub_gid sn2 sp2 `Out)
                      | _ -> None)
                  | None -> None
                in
                (* store slot: scatter coordinate (1-based -> -1) or the
                   iteration counter *)
                let slot =
                  match place_opt with
                  | Some p ->
                      C.BinOp
                        (C.Sub, C.Cast (C.Basic "int64_t", p), C.LitInt 1)
                  | None ->
                      C.Cast
                        ( C.Basic "int64_t",
                          C.UnaryOp (C.PostInc, C.Id ctr) )
                in
                let scalar_store =
                  [
                    C.Expr
                      (C.BinOp
                         ( C.Assign,
                           C.Index
                             ( C.Cast
                                 ( C.Pointer (elem_ty, []),
                                   C.Member (res_v, "data") ),
                               slot ),
                           C.Call
                             ( "SISAL_CAST",
                               [ C.Id (string_of_c_type elem_ty); body_val ] )
                         ));
                  ]
                in
                (* Shaped gather `array_dv(e1,..,ek) of`: the RETURNS DV_GATHER's
                   dope port is fed by DV_MAKE_DOPE, whose extent operands are
                   loop-invariant RETURNS boundary inputs wired from the loop
                   compound boundary -- so their C exprs are preheader-safe.
                   Collect them in DV_MAKE_DOPE port order. *)
                let shaped_exts =
                  match gnid with
                  | None -> None
                  | Some gnid -> (
                      let dope_src =
                        ES.fold
                          (fun ((sn, _), (dn, dp), _) a ->
                            if dn = gnid && dp = 2 then Some sn else a)
                          g_ret_gr.eset None
                      in
                      match dope_src with
                      | Some mnid -> (
                          match NM.find_opt mnid g_ret_gr.nmap with
                          | Some (Simple (_, DV_MAKE_DOPE, _, _, _)) ->
                              let ext_ports =
                                ES.fold
                                  (fun ((sn, sp), (dn, dp), _) acc ->
                                    if dn = mnid && dp >= 2 && sn = 0 then
                                      (dp, sp) :: acc
                                    else acc)
                                  g_ret_gr.eset []
                                |> List.sort compare
                              in
                              Some
                                (List.map
                                   (fun (_, extp) ->
                                     match
                                       ES.fold
                                         (fun ((sn2, sp2), (dn2, dp2), _) a ->
                                           if dn2 = g_ret_nid && dp2 = extp
                                           then Some (sn2, sp2)
                                           else a)
                                         loop_gr.eset None
                                     with
                                     | Some (sn2, sp2) ->
                                         get_expr env_loop sub_gid sn2 sp2 `Out
                                     | None ->
                                         failwith
                                           "shaped gather: extent not wired \
                                            into RETURNS")
                                   ext_ports)
                          | _ -> None)
                      | None -> None)
                in
                match shaped_exts with
                | Some exts ->
                    (* Extent-driven sizing: the TEST compare is never read, so
                       non-additive inductions (m := old m * 4) are fine. *)
                    if is_arr_elem then
                      (* array_dv element: element byte size and rank are RUNTIME
                         values read off the incoming element's dope; allocation
                         happens lazily on the first iteration (leading dim from
                         the declared extent, the rest from the element). *)
                      let ext0 = List.hd exts in
                      let pre' =
                        [
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 res_v,
                                 C.Call ("sisal_array_empty", []) ));
                          C.Decl (C.Basic "int32_t", ctr, Some (C.LitInt 0));
                        ]
                      in
                      let store' =
                        [
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 res_v,
                                 C.Call
                                   ( "sisal_array_shaped_store",
                                     [
                                       res_v;
                                       body_val;
                                       C.Cast (C.Basic "int64_t", ext0);
                                       slot;
                                     ] ) ));
                        ]
                      in
                      ( pre @ pre',
                        store @ store',
                        (ret_out_port, res_v) :: binds )
                    else
                      let k = List.length exts in
                      let total =
                        List.fold_left
                          (fun a e -> C.BinOp (C.Mul, a, e))
                          (List.hd exts) (List.tl exts)
                      in
                      let dims_sets =
                        (* alloc_empty already sets dims[0] for rank 1 *)
                        if k = 1 then []
                        else
                          List.mapi
                            (fun j e ->
                              C.Expr
                                (C.BinOp
                                   ( C.Assign,
                                     C.Index
                                       (C.Member (res_v, "dims"), C.LitInt j),
                                     C.Cast (C.Basic "int64_t", e) )))
                            exts
                      in
                      let pre' =
                        [
                          C.Decl (C.Basic "int32_t", ctr, Some (C.LitInt 0));
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 res_v,
                                 alloc_array_call (C.LitInt k) (C.LitInt tid)
                                   (C.Cast (C.Basic "uint64_t", total))
                                   elem_ty ));
                        ]
                        @ dims_sets
                      in
                      ( pre @ pre',
                        store @ scalar_store,
                        (ret_out_port, res_v) :: binds )
                | None ->
                    (* Bare gather: read the bound off the TEST compare NODE (cond
                    is only the lowered result variable).  Find the node feeding
                    TEST boundary-out 0, assert it is `<=` for now, and lower its
                    two operands: op0 = induction carry (holds the seed in the
                    preheader), op1 = upper bound. *)
                    let cmp =
                      ES.fold
                        (fun (src, dst, _) a ->
                          if dst = (0, 0) then Some src else a)
                        test_gr.eset None
                    in
                    let cn =
                      match cmp with
                      | Some (c, _) -> c
                      | None -> failwith "for-initial gather: no TEST compare"
                    in
                    let cmp_sym =
                      match NM.find_opt cn test_gr.nmap with
                      | Some (Simple (_, s, _, _, _)) -> s
                      | _ -> failwith "for-initial gather: no TEST compare node"
                    in
                    let lower_op p =
                      match
                        ES.fold
                          (fun ((s, sp), (d, dp), _) a ->
                            if d = cn && dp = p then Some (s, sp) else a)
                          test_gr.eset None
                      with
                      | Some (s, sp) -> get_expr e_test1 test_gid s sp `Out
                      | None ->
                          failwith
                            "for-initial gather: missing TEST compare operand"
                    in
                    (* op0 = induction var (holds the seed in the preheader), op1 = bound *)
                    let op0 = lower_op 0 and op1 = lower_op 1 in
                    let seed =
                      Printf.sprintf "__gseed_%d_%d" sub_gid ret_out_port
                    in
                    let bound =
                      Printf.sprintf "__gbound_%d_%d" sub_gid ret_out_port
                    in
                    (* iteration count from the bound + comparison op (assumes step +/-1):
                    i<=n: n-seed+1 ; i<n: n-seed ; i>=n: seed-n+1 ; i>n: seed-n. *)
                    let sd = C.Id seed and bd = C.Id bound in
                    let dec a b = C.BinOp (C.Sub, a, b)
                    and inc e = C.BinOp (C.Add, e, C.LitInt 1) in
                    let size =
                      match cmp_sym with
                      | LESSER_EQUAL -> inc (dec bd sd)
                      | LESSER -> dec bd sd
                      | GREATER_EQUAL -> inc (dec sd bd)
                      | GREATER -> dec sd bd
                      | _ ->
                          failwith
                            "for-initial gather: loop test is not a </<=/>/>= \
                             comparison"
                    in
                    (* When the gathered element is itself an array_dv (elem_ty ==
                       sisal_array_t), FLATTEN by copying each iteration's buffer into a
                       growing rank-2 result -- NOT a boxed descriptor per iteration (which
                       would make a nested array_dv[array_dv[..]]).  Grows per real
                       iteration, so it also sidesteps the static bound-seed sizing.  The
                       scalar case is unchanged (static alloc + store at __gctr) for now. *)
                    let pre' =
                      if is_arr_elem then
                        [
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 res_v,
                                 C.Call ("sisal_array_empty", []) ));
                        ]
                      else
                        [
                          C.Decl (C.Basic "int32_t", seed, Some op0);
                          (* carry holds the seed in the preheader *)
                          C.Decl (C.Basic "int32_t", bound, Some op1);
                          C.Decl (C.Basic "int32_t", ctr, Some (C.LitInt 0));
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 res_v,
                                 alloc_array_call (C.LitInt 1) (C.LitInt tid)
                                   (C.Cast (C.Basic "uint64_t", size))
                                   elem_ty ));
                        ]
                    in
                    let store' =
                      if is_arr_elem then
                        [
                          C.Expr
                            (C.BinOp
                               ( C.Assign,
                                 res_v,
                                 C.Call
                                   ( "sisal_array_concat_grow",
                                     [ res_v; body_val ] ) ));
                        ]
                      else scalar_store
                    in
                    (pre @ pre', store @ store', (ret_out_port, res_v) :: binds)))
      ([], [], [])
      (for_initial_gather_ports g_ret_gr)
  in
  let is_gather_port p = List.mem_assoc p gather_binds in
  (* Backedge copies for the loop-carried MERGE phis. Each MERGE takes its body feedback on
     input port 2; copy that into the MERGE variable at the bottom of the loop body, after
     the body captures. Every RHS resolves to a loop-scope bodycap capture, a snapshot
     distinct from any MERGE variable, so these copies cannot read a value another copy is
     about to overwrite: no SSA swap / lost-copy hazard, independent of copy order. *)
  let merge_backedge_copies =
    NM.fold
      (fun mnid mnode acc ->
        match mnode with
        | Simple (_, MERGE, _, _, _) -> (
            match
              ES.fold
                (fun ((sn, sp), (dn, dp), _) a ->
                  if dn = mnid && dp = 2 then Some (sn, sp) else a)
                loop_gr.eset None
            with
            | Some (sn, sp) ->
                let lhs = get_expr env_loop sub_gid mnid 0 `Out in
                let rhs = get_expr env_loop sub_gid sn sp `Out in
                acc @ [ C.Expr (C.BinOp (C.Assign, lhs, rhs)) ]
            | None -> acc)
        | _ -> acc)
      loop_gr.nmap []
  in
  (* Bug 5: after BODY, update carry-slot C variables from BODY outputs *)
  let carry_update_stmts, env_loop =
    update_carry_slots body_nid body_gid body_gr e_body env_loop
  in

  (* Run TEST a second time inside the while body.  Its variables are already
     pre-declared (in seen_decls from the first run), so only assignments are
     emitted — no duplicate declarations in C. *)
  let env_test2 =
    {
      env_loop with
      parent_env = Some env_loop;
      curr_gid = test_gid;
      curr_gr = test_gr;
      parent_map = IntMap.add test_gid (sub_gid, test_nid) env_loop.parent_map;
    }
  in
  let test_stmts2, e_test2 =
    lower_graph env_test2 loop_gr test_nid test_gr test_gid
  in
  let env_loop =
    {
      env_loop with
      var_map = e_test2.var_map;
      type_table = e_test2.type_table;
      seen_decls = e_test2.seen_decls;
    }
  in
  let while_loop =
    C.While
      ( cond,
        body_stmts @ body_capture_assigns @ gather_store @ merge_backedge_copies
        @ carry_update_stmts @ test_stmts2 )
  in
  (* FinalVal ZERO-TRIP correctness: a RETURNS consumer of a BODY output that
     carries a MERGE backedge value must read the MERGE carry variable, not
     the bodycap snapshot.  After any iteration the two are equal (the
     backedge copy runs at the bottom of the body), but when the loop never
     runs the bodycap was never assigned while the MERGE still holds the
     INIT seed -- `value of X` must yield that seed (found via
     find_pivot(N,N,..) in gaussj_perm_dv returning 0 -> NaN).  The BODY may
     export the same inner value on SEVERAL boundary ports (one feeds the
     backedge, another the RETURNS), so match by the port's INNER source,
     not the port number.  Rebinding here is safe: every loop statement
     (captures, backedge copies, TEST re-run) is already built. *)
  let env_loop =
    (* inner source of a BODY boundary out port *)
    let inner_src p =
      ES.fold
        (fun ((isn, isp), (dn, dp), _) a ->
          if dn = 0 && dp = p then Some (isn, isp) else a)
        body_gr.eset None
    in
    NM.fold
      (fun mnid mnode e ->
        match mnode with
        | Simple (_, MERGE, _, _, _) -> (
            match
              ES.fold
                (fun ((sn, sp), (dn, dp), _) a ->
                  if dn = mnid && dp = 2 && sn = body_nid then Some sp else a)
                loop_gr.eset None
            with
            | Some sp_backedge -> (
                match inner_src sp_backedge with
                | Some src ->
                    let merge_expr = get_expr e sub_gid mnid 0 `Out in
                    ES.fold
                      (fun ((isn, isp), (dn, dp), _) e' ->
                        if dn = 0 && (isn, isp) = src then
                          {
                            e' with
                            var_map =
                              FullPortMap.add
                                (sub_gid, body_nid, dp, `Out)
                                merge_expr e'.var_map;
                          }
                        else e')
                      body_gr.eset e
                | None -> e)
            | None -> e)
        | _ -> e)
      loop_gr.nmap env_loop
  in
  let ret_nid, ret_gr =
    match find_subgraph loop_gr "RETURNS" with
    | Some x -> x
    | _ -> failwith "no RET"
  in
  let ret_gid =
    try GidMap.find (sub_gid, ret_nid) env.gid_table with _ -> -1
  in
  let env_ret =
    {
      env_loop with
      parent_env = Some env_loop;
      curr_gid = ret_gid;
      curr_gr = ret_gr;
      parent_map = IntMap.add ret_gid (sub_gid, ret_nid) env_loop.parent_map;
    }
  in
  let ret_stmts, e_ret = lower_graph env_ret loop_gr ret_nid ret_gr ret_gid in
  let out_pids =
    ES.fold
      (fun ((sn, sp), _, _) acc -> if sn = nid then IntSet.add sp acc else acc)
      gr.eset IntSet.empty
    |> IntSet.elements
  in
  let props, final_env =
    List.fold_left
      (fun (acc, e) dp ->
        if is_gather_port dp then
          (* gather port: bind to the alloc'd-and-filled array, not the placeholder *)
          let stmts, e' =
            assign_with_cast e gid nid dp `Out (List.assoc dp gather_binds)
          in
          (acc @ stmts, e')
        else
          match FullPortMap.find_opt (ret_gid, 0, dp, `In) e_ret.var_map with
          | Some src_expr ->
              let stmts, e' = assign_with_cast e gid nid dp `Out src_expr in
              (acc @ stmts, e')
          | None -> (
              (* Trace via ret_gr eset to find source of boundary input dp *)
              match
                ES.fold
                  (fun ((sn, sp), (dn, dp2), _) a ->
                    if dn = 0 && dp2 = dp then Some (sn, sp) else a)
                  ret_gr.eset None
              with
              | Some (sn, sp) -> (
                  match
                    FullPortMap.find_opt (ret_gid, sn, sp, `Out) e_ret.var_map
                  with
                  | Some src_expr ->
                      let stmts, e' =
                        assign_with_cast e gid nid dp `Out src_expr
                      in
                      (acc @ stmts, e')
                  | None -> (acc, e))
              | None -> (acc, e)))
      ([], { e_ret with curr_gid = gid; curr_gr = gr })
      out_pids
  in
  ( decl_stmts
    @ [
        C.Compound
          (loop_local_decls @ merge_decls @ body_capture_decls @ loop_in_stmts
         @ init_stmts @ carry_init_stmts @ copy_non_merged_stmts @ merge_init_seeds @ test_stmts1
         @ gather_pre @ [ while_loop ] @ ret_stmts @ props);
      ],
    final_env )

(** [dummy_env tm sub_gr] — a fresh empty lowering environment; the seed
    lower_to_c builds the real env from. *)
let dummy_env tm sub_gr =
  {
    tm;
    var_map = FullPortMap.empty;
    type_table = FullPortMap.empty;
    preds = FullPortMap.empty;
    curr_gid = 0;
    curr_gr = sub_gr;
    parent_env = None;
    compound_nid_in_parent = 0;
    seen_decls = StringSet.empty;
    fanout_map = PortFanout.empty;
    mandatory_ports = PortSet.empty;
    gid_table = GidMap.empty;
    parent_map = IntMap.empty;
    proc_map = IntMap.empty;
    proc_param_map = FullPortMap.empty;
    gid_name_map = IntMap.empty;
    procedures_info = IntMap.empty;
    force_gpu = false;
  }

(** [lower_procedure tm gid_table gid_name_map proc_map procedures_info_map
    nid node gr_module] — one top-level function compound to a C function:
    parameters from its Function_ty (boundary inputs in declared order), body
    via lower_graph under a fresh env, single return value or a
    FUNC_<NAME>_results struct for multi-output functions. *)
let lower_procedure tm gid_table gid_name_map proc_map procedures_info_map nid
    node gr_module =
  match node with
  | Compound (_, INTERNAL, ty_id, pr, sub_gr, _) ->
      let func_name =
        List.find_map (function Name nm -> Some nm | _ -> None) pr
        |> Option.map String.uppercase_ascii
        |> Option.map (fun n -> "func_" ^ n)
        |> Option.value ~default:"unnamed"
      in

      let all_b_ins =
        match NM.find_opt 0 sub_gr.nmap with
        | Some (Boundary (ins, _, _, _)) ->
            List.init (List.length ins) (fun i -> i)
        | _ -> []
      in
      let env_module =
        {
          (dummy_env tm gr_module) with
          gid_table;
          proc_map;
          gid_name_map;
          procedures_info = procedures_info_map;
          curr_gid = 0;
          curr_gr = gr_module;
        }
      in
      let env_init =
        {
          (dummy_env tm sub_gr) with
          gid_table;
          proc_map;
          gid_name_map;
          procedures_info = procedures_info_map;
          curr_gid = nid;
          parent_env = Some env_module;
        }
      in

      (* Seed the procedure types using the function's type definition *)
      let param_types = get_function_param_types tm ty_id in
      let env_seeded =
        List.fold_left2
          (fun env_acc pid tid ->
            let ty_val = try TM.find tid tm with _ -> Basic REAL in
            {
              env_acc with
              type_table =
                FullPortMap.add (nid, 0, pid, `Out)
                  (c_type_of_if1_ty tm ty_val)
                  env_acc.type_table;
            })
          env_init
          (List.filter (fun p -> p < List.length param_types) all_b_ins)
          param_types
      in

      let env_typed = infer_types env_seeded sub_gr nid in
      let param_tids = get_function_param_types tm ty_id in
      let params =
        List.mapi
          (fun i pid ->
            let ty =
              if i < List.length param_tids then
                let tid = List.nth param_tids i in
                c_type_of_if1_tyid tm tid
              else get_final_ty env_typed nid 0 pid `Out
            in
            let name =
              match get_port_name_from_cs sub_gr 0 pid `Out with
              | Some n -> sanitize n
              | None -> Printf.sprintf "param_%d" pid
            in
            (ty, name))
          all_b_ins
      in
      (* Seed param names so pre_declare sees them and can detect conflicts *)
      List.iter (fun (ty, name) -> Printf.fprintf stderr "DEBUG PARAM: name=%s, ty=%s\n" name (string_of_c_type ty)) params;
      let env_param_seeded =
        List.fold_left2
          (fun e pid (_, name) ->
            {
              e with
              var_map =
                FullPortMap.add (nid, 0, pid, `Out) (C.Id name) e.var_map;
              seen_decls = StringSet.add name e.seen_decls;
            })
          env_typed all_b_ins params
      in

      (* Pre-declare all locals up front; this overwrites boundary-input entries in var_map
         with the local variable names (e.g. v_g1_n__0_V instead of V) *)
      let pre_stmts, env_predecl =
        pre_declare_graph_locals env_param_seeded sub_gr nid
      in

      (* Bind each function parameter to its newly-created local declaration *)
      let bind_stmts =
        List.concat
          (List.mapi
             (fun i (ty, param_name) ->
               match
                 FullPortMap.find_opt (nid, 0, i, `Out) env_predecl.var_map
               with
               | Some (C.Id local_name) when local_name <> param_name ->
                   [
                     C.Expr
                       (C.BinOp
                          ( C.Assign,
                            C.Id local_name,
                            C.Call
                              ( "SISAL_CAST",
                                [ C.Id (string_of_c_type ty); C.Id param_name ]
                              ) ));
                   ]
               | _ -> [])
             params)
      in
      (* Bind alias symtab entries (same port, different val_name) to the canonical variable *)
      let alias_bind_stmts =
        let cs, _ = sub_gr.symtab in
        SM.fold
          (fun _ v acc ->
            if is_proc_expr env_predecl nid v.val_def then acc
            else
              let specific =
                Printf.sprintf "v_%s_n__%d_%s"
                  (scope_of gid_name_map nid)
                  v.val_def (sanitize v.val_name)
              in
              match
                FullPortMap.find_opt
                  (nid, v.val_def, v.def_port, `Out)
                  env_predecl.var_map
              with
              | Some (C.Id canonical)
                when canonical <> specific
                     && StringSet.mem specific env_predecl.seen_decls ->
                  let ty =
                    get_final_ty env_predecl nid v.val_def v.def_port `Out
                  in
                  acc
                  @ [
                      C.Expr
                        (C.BinOp
                           ( C.Assign,
                             C.Id specific,
                             C.Call
                               ( "SISAL_CAST",
                                 [ C.Id (string_of_c_type ty); C.Id canonical ]
                               ) ));
                    ]
              | _ -> acc)
          cs []
      in

      (* Determine output ports and declare their return variables up front, just like
         boundary inputs, so they are visible for the whole procedure body.
         Exclude error edges (BROADCAST_ERROR etc.) — those are exception flows, not return values. *)
      let out_pids =
        ES.fold
          (fun (_, (dn, dp), ty) acc ->
            if dn = 0 && not (is_error_port ty sub_gr) then IntSet.add dp acc
            else acc)
          sub_gr.eset IntSet.empty
        |> IntSet.elements
      in
      let ret_decl_stmts, env_predecl =
        List.fold_left
          (fun (acc_stmts, e) pid ->
            let ty = get_final_ty e nid 0 pid `In in
            let name =
              get_c_name e.proc_map e.gid_name_map nid 0 pid `In sub_gr
            in
            if not (StringSet.mem name e.seen_decls) then
              let init_val = default_init_for ty in
              ( acc_stmts @ [ C.Decl (ty, name, init_val) ],
                {
                  e with
                  seen_decls = StringSet.add name e.seen_decls;
                  var_map =
                    FullPortMap.add (nid, 0, pid, `In) (C.Id name) e.var_map;
                } )
            else (acc_stmts, e))
          ([], env_predecl) out_pids
      in

      (* lower_graph will call pre_declare_graph_locals again, but seen_decls already has
         all names, so it produces no new decls — body is purely the node computations *)
      let body, env_after = lower_graph env_predecl sub_gr nid sub_gr nid in

      (* Assign computed results into the pre-declared return variables *)
      let ret_assign_stmts =
        List.filter_map
          (fun pid ->
            let ty = get_final_ty env_after nid 0 pid `In in
            let ret_name =
              get_c_name env_after.proc_map env_after.gid_name_map nid 0 pid `In
                sub_gr
            in
            match
              ES.fold
                (fun (src, dst, _) acc ->
                  if dst = (0, pid) then Some src else acc)
                sub_gr.eset None
            with
            | Some (sn, sp) ->
                let src_expr = get_expr env_after nid sn sp `Out in
                Some
                  (C.Expr
                     (C.BinOp
                        ( C.Assign,
                          C.Id ret_name,
                          C.Call
                            ( "SISAL_CAST",
                              [ C.Id (string_of_c_type ty); src_expr ] ) )))
            | None -> None)
          out_pids
      in

      let res_struct_name = String.uppercase_ascii func_name ^ "_results" in
      if List.length out_pids = 1 then
        let pid = List.hd out_pids in
        let ty = get_final_ty env_after nid 0 pid `In in
        let ret_name =
          get_c_name env_after.proc_map env_after.gid_name_map nid 0 pid `In
            sub_gr
        in
        let cast_ret =
          C.Call ("SISAL_CAST", [ C.Id (string_of_c_type ty); C.Id ret_name ])
        in
        {
          C.return_ty = ty;
          name = func_name;
          params;
          body =
            pre_stmts @ bind_stmts @ alias_bind_stmts @ ret_decl_stmts @ body
            @ ret_assign_stmts
            @ [ C.Return (Some cast_ret) ];
          extern_c = true;
        }
      else
        let res_obj_name = "__res_obj" in
        let assignments =
          List.map
            (fun pid ->
              let ty = get_final_ty env_after nid 0 pid `In in
              let ret_name =
                get_c_name env_after.proc_map env_after.gid_name_map nid 0 pid
                  `In sub_gr
              in
              C.Expr
                (C.BinOp
                   ( C.Assign,
                     C.Member (C.Id res_obj_name, "res_" ^ string_of_int pid),
                     C.Call
                       ( "SISAL_CAST",
                         [ C.Id (string_of_c_type ty); C.Id ret_name ] ) )))
            out_pids
        in
        {
          C.return_ty = C.Basic ("struct " ^ res_struct_name);
          name = func_name;
          params;
          body =
            pre_stmts @ bind_stmts @ alias_bind_stmts @ ret_decl_stmts @ body
            @ ret_assign_stmts
            @ [
                C.Decl
                  (C.Basic ("struct " ^ res_struct_name), res_obj_name, None);
              ]
            @ assignments
            @ [ C.Return (Some (C.Id res_obj_name)) ];
          extern_c = true;
        }
  | _ -> failwith "not compound"

(** [build_global_gid_table root_nid gr starting_gid] — assign a globally
    unique gid to every compound, keyed by (parent_gid, nid), plus a readable
    scope name per gid; gids are the C-name scoping backbone
    (v_<scope>_<gid>_... variables). *)
let build_global_gid_table root_nid gr starting_gid =
  let table = Hashtbl.create 64 in
  let name_map = Hashtbl.create 64 in
  let rec visit parent_gid sub_gr counter =
    NM.fold
      (fun nid node ctr ->
        match node with
        | Compound (_, _, _, pr, inner_gr, _) ->
            let gid = ctr + 1 in
            Hashtbl.replace table (parent_gid, nid) gid;
            let cname =
              match
                List.find_map
                  (function Name n -> Some (sanitize n) | _ -> None)
                  pr
              with
              | Some n -> n
              | None -> "g" ^ string_of_int gid
            in
            Hashtbl.replace name_map gid cname;
            visit gid inner_gr gid
        | _ -> ctr)
      sub_gr.nmap counter
  in
  let final_counter = visit root_nid gr starting_gid in
  let gid_map =
    Hashtbl.fold (fun k v m -> GidMap.add k v m) table GidMap.empty
  in
  let nmap =
    Hashtbl.fold (fun k v m -> IntMap.add k v m) name_map IntMap.empty
  in
  (gid_map, final_counter, nmap)

(** [collect_typemaps g acc] — every subgraph's typemap, collected for
    whole-program passes (struct/union emission, signatures).  Ids are
    allocated per graph; the merge discipline in to_if1 keeps sibling id
    spaces collision-free. *)
let rec collect_typemaps g acc =
  let _, tm, _ = g.typemap in
  let acc = tm :: acc in
  NM.fold (fun _ node acc ->
    match node with
    | Compound (_, _, _, _, sub, _) -> collect_typemaps sub acc
    | _ -> acc
  ) g.nmap acc

(** [lower_to_c tm gr filename] — the backend entry point: build the gid
    table and procedures info, emit record/union struct definitions
    (topologically), then lower every procedure; returns the complete C
    compilation unit. *)
let lower_to_c tm gr filename =
  TM.iter (fun id ty -> Printf.fprintf stderr "DEBUG ROOT TYPEMAP: id=%d\n" id) tm;
  let procedures_info =
    NM.fold
      (fun nid node acc ->
        match node with
        | Compound (_, INTERNAL, _, pr, sub_gr, _)
          when get_compound_type pr = If1_procedure ->
            (nid, node, sub_gr) :: acc
        | _ -> acc)
      gr.nmap []
  in
  let all_tms =
    let acc = collect_typemaps gr [] in
    List.fold_left
      (fun acc (_, _, sub_gr) -> collect_typemaps sub_gr acc)
      acc procedures_info
  in
  let global_tm =
    List.fold_left
      (fun acc tm -> TM.fold (fun id ty acc -> TM.add id ty acc) tm acc)
      TM.empty all_tms
  in
  let dummy_gr = { gr with typemap = (65536, global_tm, MM.empty) } in
  let alias_map, clean_tm = Ir.Cleanup.build_type_equivalence_classes dummy_gr in
  Apple_helpers.global_alias_map := alias_map;
  let tm = clean_tm in

  let global_table, gid_name_map =
    List.fold_left
      (fun (acc_tbl, acc_names, next_gid) (nid, _, sub_gr) ->
        let tbl, last_gid, nmap = build_global_gid_table nid sub_gr next_gid in
        let acc_tbl = GidMap.add (0, nid) nid acc_tbl in
        let acc_names = IntMap.union (fun _ a _ -> Some a) acc_names nmap in
        ( GidMap.fold (fun k v m -> GidMap.add k v m) tbl acc_tbl,
          acc_names,
          last_gid + 1000 ))
      (GidMap.empty, IntMap.empty, 10000)
      procedures_info
    |> fun (t, n, _) -> (t, n)
  in

  let proc_map =
    List.fold_left
      (fun m (nid, node, _) ->
        match node with
        | Compound (_, INTERNAL, _, pr, _, _) -> (
            let func_name =
              List.find_map (function Name nm -> Some nm | _ -> None) pr
              |> Option.map String.uppercase_ascii
              |> Option.map (fun n -> "func_" ^ n)
            in
            match func_name with Some n -> IntMap.add nid n m | None -> m)
        | _ -> m)
      IntMap.empty procedures_info
  in

  let procedures_info_map =
    List.fold_left
      (fun m (nid, _, sub_gr) -> IntMap.add nid sub_gr m)
      IntMap.empty procedures_info
  in

  let procedures =
    List.map
      (fun (nid, node, sub_gr) ->
        lower_procedure tm global_table gid_name_map proc_map
          procedures_info_map nid node gr)
      procedures_info
  in

  let result_struct_decls =
    List.filter_map
      (fun (nid, node, sub_gr) ->
        match node with
        | Compound (_, INTERNAL, _, pr, _, _) ->
            let func_name =
              List.find_map (function Name nm -> Some nm | _ -> None) pr
              |> Option.map String.uppercase_ascii
              |> Option.map (fun n -> "func_" ^ n)
              |> Option.value ~default:"unnamed"
            in
            let out_pids =
              ES.fold
                (fun (_, (dn, dp), ty) acc ->
                  if dn = 0 && not (is_error_port ty sub_gr) then
                    IntSet.add dp acc
                  else acc)
                sub_gr.eset IntSet.empty
              |> IntSet.elements
            in
            if List.length out_pids > 1 then
              let results =
                List.map
                  (fun pid ->
                    let env_tmp =
                      {
                        (dummy_env tm sub_gr) with
                        curr_gr = sub_gr;
                        gid_table = global_table;
                        proc_map;
                        gid_name_map;
                        procedures_info = procedures_info_map;
                        curr_gid = nid;
                      }
                    in
                    ( "res_" ^ string_of_int pid,
                      get_final_ty
                        (infer_types env_tmp sub_gr nid)
                        nid 0 pid `In ))
                  out_pids
              in
              Some
                (C.Type
                   (C.Struct
                      (String.uppercase_ascii func_name ^ "_results", results)))
            else None
        | _ -> None)
      procedures_info
  in

  let field_record_deps clean_tm id =
    let rec chain lbl acc =
      match TM.find_opt lbl clean_tm with
      | Some (Record (0, next, "")) -> chain next acc
      | Some (Record (fty, next, _)) ->
          let acc =
            match TM.find_opt fty clean_tm with
            | Some (Record _) | Some (Union _) -> fty :: acc
            | _ -> acc
          in
          chain next acc
      | Some (Union (0, next, "")) -> chain next acc
      | Some (Union (fty, next, _)) ->
          let acc =
            match TM.find_opt fty clean_tm with
            | Some (Record _) | Some (Union _) -> fty :: acc
            | _ -> acc
          in
          chain next acc
      | _ -> acc
    in
    chain id []
  in

  let rec emit_type clean_tm id (acc, s) =
    if IntSet.mem id s then (acc, s)
    else
      let s = IntSet.add id s in
      let deps = field_record_deps clean_tm id in
      let acc, s = List.fold_left (fun st d -> emit_type clean_tm d st) (acc, s) deps in
      match TM.find_opt id clean_tm with
      | Some (Record _) ->
          let fields = collect_record_fields clean_tm id in
          if fields = [] then (acc, s)
          else
            ( acc @ [ C.Type (C.Struct ("struct_rec_" ^ string_of_int id, fields)) ],
              s )
      | Some (Union _) ->
          let tags = Apple_helpers.collect_union_tags_with_ids clean_tm id in
          if tags = [] then (acc, s)
          else
            let enum_fields_str =
              List.map (fun (tag_id, name, _) ->
                "union_" ^ string_of_int id ^ "_" ^ name ^ " = " ^ string_of_int tag_id
              ) tags
              |> String.concat ",\n  "
            in
            let enum_decl =
              C.Raw (Printf.sprintf "enum union_tag_%d {\n  %s\n};" id enum_fields_str)
            in
            let union_fields =
              List.map (fun (_, name, fty) -> (name, fty)) tags
            in
            let struct_decl =
              C.Type (C.Struct ("union_un_" ^ string_of_int id, [
                ("tag", C.Basic "int32_t");
                ("val", C.Union ("union_val_" ^ string_of_int id, union_fields))
              ]))
            in
            let constructors =
              List.map (fun (tag_id, name, fty) ->
                let fty_str = Ir.C_ast_print.string_of_c_type fty in
                C.Raw (Printf.sprintf
                  "inline struct union_un_%d make_union_%d_%s(%s val) {\n\
                   \  struct union_un_%d tmp = {};\n\
                   \  tmp.tag = %d;\n\
                   \  tmp.val.%s = val;\n\
                   \  return tmp;\n\
                   }"
                  id id name fty_str id tag_id name)
              ) tags
            in
            ( acc @ [ enum_decl; struct_decl ] @ constructors, s )
      | _ -> (acc, s)
  in

  let all_records =
    TM.fold
      (fun id ty acc ->
        match ty with Record _ | Union _ -> id :: acc | _ -> acc)
      clean_tm []
  in

  let all_record_decls, _ =
    List.fold_left (fun st id -> emit_type clean_tm id st) ([], IntSet.empty) all_records
  in

  let sizeof_type_id tm tid =
    let tid =
      match TM.find_opt tid alias_map with
      | Some leader -> leader
      | None -> tid
    in
    match TM.find_opt tid tm with
    | Some (Basic b) ->
        let cty = Apple_helpers.c_type_of_if1_basic b in
        "sizeof(" ^ Ir.C_ast_print.string_of_c_type cty ^ ")"
    | Some (Record (_, _, name) as ty) ->
        let sname = String.lowercase_ascii name in
        if sname = "int" || sname = "integer" || sname = "int32" ||
           sname = "double" || sname = "double_real" || sname = "float" ||
           sname = "real" || sname = "bool" || sname = "boolean" then
          let cty = Apple_helpers.c_type_of_if1_ty tm ty in
          "sizeof(" ^ Ir.C_ast_print.string_of_c_type cty ^ ")"
        else
          "sizeof(struct struct_rec_" ^ string_of_int tid ^ ")"
    | Some (Union _) ->
        "sizeof(struct union_un_" ^ string_of_int tid ^ ")"
    | Some (Array_dv _) | Some (Array_ty _) ->
        "sizeof(sisal_array_t)"
    | _ ->
        "sizeof(sisal_array_t)"
  in

  let gen_sisal_elem_size global_tm alias_map =
    let size_groups = ref StringMap.empty in
    TM.iter (fun id ty ->
      let size_expr =
        match ty with
        | Array_dv elem_id | Array_ty elem_id -> sizeof_type_id global_tm elem_id
        | _ -> sizeof_type_id global_tm id
      in
      let existing = try StringMap.find size_expr !size_groups with Not_found -> [] in
      size_groups := StringMap.add size_expr (id :: existing) !size_groups
    ) global_tm;
    let cases =
      StringMap.fold (fun size_expr ids acc ->
        let sorted_ids = List.sort compare ids in
        let case_lines = List.map (fun id -> "        case " ^ string_of_int id ^ ":") sorted_ids in
        let case_block = String.concat "\n" case_lines ^ "\n            return " ^ size_expr ^ ";" in
        case_block :: acc
      ) !size_groups []
      |> String.concat "\n"
    in
    let code =
      "size_t sisal_elem_size(int32_t type_id) {\n" ^
      "    switch (type_id) {\n" ^
      cases ^ "\n" ^
      "        default:\n" ^
      "            return sizeof(sisal_array_t);\n" ^
      "    }\n" ^
      "}\n"
    in
    C.Raw code
  in
  let custom_elem_size_raw = gen_sisal_elem_size global_tm alias_map in

  let math_wrappers = [] in
  (* now provided by sisal_runtime.h *)

  {
    C.filename;
    includes =
      [
        "stdio.h";
        "stdint.h";
        "stdbool.h";
        "math.h";
        "iostream";
        "dispatch/dispatch.h";
        "Accelerate/Accelerate.h";
        "sisal_runtime.h";
      ];
    globals =
      math_wrappers @ all_record_decls @ result_struct_decls @ [ custom_elem_size_raw ]
      @ List.map (fun p -> C.Prototype p) procedures;
    procedures = List.rev procedures;
  }
