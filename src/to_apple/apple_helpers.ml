(** apple_helpers.ml: Utility functions for IF1 to C-AST lowering on Apple
    Silicon. Provides helpers for name sanitization, type mapping, expression
    resolution, and graph traversal. *)

open Ir.If1
open Apple_env

(** [contains_substr s sub] returns true if [sub] is a substring of [s]. *)
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

(** [sanitize name] transforms a Sisal identifier into a valid C identifier. It
    removes "OLD" prefixes, replaces spaces with underscores, and converts to
    lowercase. *)
let sanitize name =
  let s =
    if String.starts_with ~prefix:"OLD " name then
      String.sub name 4 (String.length name - 4)
    else if String.starts_with ~prefix:"OLD_" name then
      String.sub name 4 (String.length name - 4)
    else name
  in
  let s =
    String.map
      (fun c ->
        if
          (c >= 'a' && c <= 'z')
          || (c >= 'A' && c <= 'Z')
          || (c >= '0' && c <= '9')
          || c = '_'
        then c
        else '_')
      s
  in
  String.lowercase_ascii s

(** [var_name ~tag g n p dir] generates a unique C variable name for an IF1
    port. Format: v_g[gid]_[tag]_n[node_id]_p[port_id]_[i/o] *)
let var_name ?(tag = "") g n p dir =
  let d_str = match dir with `In -> "i" | `Out -> "o" in
  if tag <> "" then Printf.sprintf "v_g%d_%s_n%d_p%d_%s" g tag n p d_str
  else Printf.sprintf "v_g%d_n%d_p%d_%s" g n p d_str

(** [get_port_name gr nid pid _dir] looks up a port's name in the graph's symbol
    table. *)
let get_port_name gr nid pid _dir =
  let cs, _ps = gr.symtab in
  SM.fold
    (fun _ v acc ->
      if acc <> None then acc
      else if v.val_def = nid && v.def_port = pid then
        Some (sanitize v.val_name)
      else acc)
    cs None

(** [c_type_of_if1_basic b] maps a basic IF1 scalar type to a C type string. *)
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

(** [c_type_of_if1_ty tm ty] maps an IF1 type to its corresponding C-AST type.
*)
let c_type_of_if1_ty tm ty =
  match ty with
  | Basic b -> c_type_of_if1_basic b
  | Array_dv _ | Array_ty _ -> C.Basic "sisal_array_t"
  | Record (id, _, _) -> (
      match id with
      | 1 -> C.Basic "bool"
      | 2 | 10 | 11 | 23 | 24 | 62 | 63 | 75 | 76 -> C.Basic "uint8_t"
      | 3 -> C.Basic "char"
      | 4 | 17 | 30 | 43 | 56 | 69 -> C.Basic "double"
      | 8 | 21 | 34 | 47 | 60 | 73 -> C.Basic "float"
      | 6 | 19 | 32 | 45 | 58 | 71 -> C.Basic "int32_t"
      | 7 | 20 | 33 | 46 | 59 | 72 -> C.Basic "int64_t"
      | 13 | 26 | 39 | 52 | 65 | 78 -> C.Basic "uint64_t"
      | 5 | 18 | 31 | 44 | 57 | 70 -> C.Basic "half"
      | 9 | 22 | 35 | 48 | 61 | 74 -> C.Basic "int16_t"
      | 12 | 25 | 38 | 51 | 64 | 77 -> C.Basic "uint32_t"
      | _ -> C.Basic ("struct struct_rec_" ^ string_of_int id))
  | Union (id, _, _) -> C.Basic ("union union_un_" ^ string_of_int id)
  | _ -> C.Basic "float"

(** [type_id_of_if1_ty _tm ty] returns the runtime type ID for a given IF1 type.
*)
let type_id_of_if1_ty _tm ty =
  match ty with
  | Basic REAL -> 0
  | Basic DOUBLE -> 1
  | Basic INTEGRAL -> 2
  | Basic BOOLEAN -> 3
  | Array_dv _ | Array_ty _ -> 10
  | _ -> 0

(** [get_expr env g n p dir] recursively resolves an IF1 port to a C expression.
    It handles: 1. Direct variable mappings from [env.var_map]. 2. Boundary
    crossings between parent and child scopes. 3. Literal values. 4. Dataflow
    predecessors via [env.preds]. 5. Special cases like RANGEGEN index
    variables. *)
let rec get_expr ?(visited = PortSet.empty) env g n p dir =
  let () =
    if !Ir.Debug.level > 2 then
      Printf.eprintf "DEBUG: get_expr(gid=%d, node=%d, port=%d, dir=%s)\n" g n p
        (match dir with `In -> "In" | `Out -> "Out")
  in
  let res =
    if PortSet.mem (g, n, p, dir) visited then begin
      if !Ir.Debug.level > 2 then
        Printf.eprintf "DEBUG: cycle detected for %d:%d:%d\n" g n p;
      C.Id (var_name g n p dir)
    end
    else
      let visited = PortSet.add (g, n, p, dir) visited in
      match FullPortMap.find_opt (g, n, p, dir) env.var_map with
      | Some e ->
          if !Ir.Debug.level > 2 then
            Printf.eprintf "DEBUG: found in var_map: %s\n"
              (Ir.C_ast_print.string_of_expr e);
          e
      | None -> (
          (* If we are looking for a boundary output of some graph G, and it's not in
             our current var_map, it might be in a parent environment if we are nested.
             Reset visited when crossing env boundary so the parent can check its own
             var_map without being short-circuited by the cycle-detection set. *)
          match env.parent_env with
          | Some p_env when n = 0 && dir = `Out ->
              if !Ir.Debug.level > 2 then
                Printf.eprintf
                  "DEBUG: recursing to parent for boundary param %d\n" p;
              get_expr ~visited:PortSet.empty p_env g n p dir
          | _ -> (
              (* Heuristic for RANGEGEN index variable: search parents for closest enclosing BODY *)
              let is_rangegen =
                match NM.find_opt n env.curr_gr.nmap with
                | Some (Simple (_, RANGEGEN, _, _, _)) -> true
                | _ -> false
              in
              if is_rangegen && n <> 0 && p = 0 && dir = `Out then
                let rec find_idx e =
                  if e.curr_gid >= 1_000_000 then
                    Some (C.Id (Printf.sprintf "v_idx_g%d" e.curr_gid))
                  else
                    match e.parent_env with
                    | Some pe -> find_idx pe
                    | None -> None
                in
                match find_idx env with
                | Some ie -> ie
                | None -> C.Id (var_name g n p dir)
              else
                match FullPortMap.find_opt (g, n, p, dir) env.preds with
                | Some (sg, sn, sp, sd) -> get_expr ~visited env sg sn sp sd
                | None -> (
                    match env.parent_env with
                    | Some p_env ->
                        (* Reset visited when crossing env boundary *)
                        get_expr ~visited:PortSet.empty p_env g n p dir
                    | None -> (
                        match NM.find_opt n env.curr_gr.nmap with
                        | Some (Literal (_, ty, val_str, _)) -> (
                            match ty with
                            | CHARACTER -> C.Id val_str
                            | REAL | DOUBLE ->
                                C.LitFloat (float_of_string val_str)
                            | _ -> (
                                try C.LitInt (int_of_string val_str)
                                with _ -> C.Id val_str))
                        | _ ->
                            if n = 0 && dir = `Out then
                              match NM.find_opt 0 env.curr_gr.nmap with
                              | Some (Boundary (ins, _, _, _)) -> (
                                  match
                                    List.find_opt
                                      (fun (_, p_in, _) -> p_in = p)
                                      ins
                                  with
                                  | Some (_, _, name) ->
                                      let sname = sanitize name in
                                      if sname <> "" then C.Id sname
                                      else C.Id (var_name g n p dir)
                                  | None -> C.Id (var_name g n p dir))
                              | _ -> C.Id (var_name g n p dir)
                            else C.Id (var_name g n p dir)))))
  in
  res

(** [get_port_type env gr nid pid dir] infers the C type for a specific IF1
    port. It searches edge type annotations, boundary metadata, and falls back
    to heuristics. *)
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

  let ty_id =
    if ty_id <> 0 then ty_id
    else
      match NM.find_opt nid gr.nmap with
      | Some (Boundary (ins, outs, errs, _)) -> (
          if dir = `Out then
            let matched =
              List.find_map
                (fun (tid, p, _) -> if p = pid then Some tid else None)
                ins
            in
            Option.value matched ~default:0
          else
            let matched =
              List.find_map
                (fun (tid, p) -> if p = pid then Some tid else None)
                outs
            in
            match matched with
            | Some t -> t
            | None -> (
                match
                  List.find_map
                    (fun (tid, p) -> if p = pid then Some tid else None)
                    errs
                with
                | Some t -> t
                | None -> 0))
      | _ -> 0
  in

  (* Hardcoded basic type IDs from If1.lookup_tyid for robustness against typemap collisions/omissions *)
  let basic_opt =
    match ty_id with
    | 1 -> Some BOOLEAN
    | 3 -> Some CHARACTER
    | 4 -> Some DOUBLE
    | 6 -> Some INTEGRAL
    | 8 -> Some REAL
    | 2 -> Some BYTE
    | 5 -> Some HALF
    | 7 -> Some LONG
    | 9 -> Some SHORT
    | 10 -> Some UBYTE
    | 11 -> Some UCHAR
    | 12 -> Some UINT
    | 13 -> Some ULONG
    | 14 -> Some USHORT
    | _ -> None
  in

  match basic_opt with
  | Some b -> c_type_of_if1_basic b
  | None -> (
      try
        if ty_id = 0 then raise Not_found;
        let if1_ty = TM.find ty_id env.tm in
        c_type_of_if1_ty env.tm if1_ty
      with _ -> (
        (* Heuristics for cases with no type ID *)
        match NM.find_opt nid gr.nmap with
        | Some (Simple (_, sym, _, _, _))
          when List.mem sym
                 [
                   RANGEGEN;
                   ALIML;
                   ALIMH;
                   ASIZE;
                   DV_DIMENSION;
                   DV_NUM_RANK;
                   DV_OFFSET_AT;
                 ] ->
            C.Basic "int32_t"
        | Some (Simple (_, (DV_LOAD_LINEAR | DV_ELEMENT | AELEMENT), _, _, _))
          ->
            C.Basic "float"
        | Some (Simple (_, sym, _, _, _))
          when List.mem sym
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
                   DV_SCATTER;
                   AGATHER;
                   ASCATTER;
                   ABUILD;
                   AFILL;
                   ACREATE;
                 ] ->
            C.Basic "sisal_array_t"
        | Some (Compound (_, sym, _, pr, _, _)) ->
            let is_forall =
              List.exists (function Name n -> n = "FORALL" | _ -> false) pr
            in
            if is_forall || sym = STREAM || sym = MAT then
              C.Basic "sisal_array_t"
            else C.Basic "float"
        | Some (Boundary (ins, _outs, _, _)) ->
            let is_range_related =
              let matched_name =
                List.find_opt
                  (fun (_, p, name) ->
                    let sname = String.lowercase_ascii name in
                    p = pid
                    && (sname = "i" || sname = "index" || sname = "lo"
                      || sname = "hi" || sname = "count"))
                  ins
              in
              let has_rangegen =
                NM.exists
                  (fun _ n ->
                    match n with
                    | Simple (_, RANGEGEN, _, _, _) -> true
                    | _ -> false)
                  gr.nmap
              in
              Option.is_some matched_name || (has_rangegen && pid = 0)
            in
            if nid = 0 && dir = `Out then
              if is_range_related then C.Basic "int32_t"
              else C.Basic "sisal_array_t"
            else if nid = 0 && dir = `In then
              if is_range_related then C.Basic "int32_t" else C.Basic "float"
            else C.Basic "float"
        | _ -> C.Basic "float"))

(** [get_elem_type env gr nid] retrieves the element type of an array node. *)
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

(** [string_of_pragma p] extracts the string value from a pragma. *)
let string_of_pragma = function
  | Name s | Ast_type s | Subscript s -> s
  | _ -> ""

(** [collect_record_fields tm label] recursively extracts field names and types
    for a Sisal record structure. *)
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

(** [find_subgraph gr name] locates a named subgraph (e.g., "BODY", "GENERATOR")
    within a graph based on pragma annotations. *)
let find_subgraph gr name =
  let target = String.uppercase_ascii name in
  let res =
    NM.choose_opt
      (NM.filter
         (fun _ n ->
           match n with
           | Compound (_, _, _, pr, _, _) ->
               List.exists
                 (function
                   | Name s | Ast_type s | Subscript s ->
                       String.uppercase_ascii s = target
                   | _ -> false)
                 pr
           | _ -> false)
         gr.nmap)
  in
  res
  |> Option.map (fun (id, n) ->
      match n with Compound (_, _, _, _, g, _) -> (id, g) | _ -> assert false)

(** [get_subgraph_errors env gid cid] returns the error output expressions for a
    compound node's subgraph. *)
let get_subgraph_errors env gid cid =
  match NM.find_opt cid env.curr_gr.nmap with
  | Some (Compound (sub_cid, _, _, _, sub_gr, _)) -> (
      let sub_gid = alloc_gid env.gid_table gid sub_cid in
      match NM.find_opt 0 sub_gr.nmap with
      | Some (Boundary (_, outs, errs, _)) ->
          List.mapi
            (fun i _ ->
              let pid = List.length outs + i in
              get_expr env sub_gid 0 pid `Out)
            errs
      | _ -> [])
  | _ -> []

(** [find_boundary_selects gr] identifies SELECT nodes that feed directly into
    the graph's boundary outputs, acting as phi-node/merge points.

    In an IF subgraph the SELECT nodes are the phi/merge points: each one sits
    at the boundary, takes (predicate, then-result, else-result) as inputs, and
    its output is the subgraph result for that port. *)
let find_boundary_selects gr =
  ES.fold
    (fun ((sn, _sp), (dn, dp), _) acc ->
      if dn = 0 then
        match NM.find_opt sn gr.nmap with
        | Some (Simple (_, SELECT, _, _, _)) -> (sn, dp) :: acc
        | _ -> acc
      else acc)
    gr.eset []

(** [topo_sort gr] performs a Kahn-style topological sort of the graph's nodes
    to ensure that definitions precede uses in the generated C code. *)
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
