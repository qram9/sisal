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

(** [sanitize name] transforms a Sisal identifier into a valid C identifier. *)
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
  s

(** [get_port_name env gr nid pid dir] looks up a port's name in the graph's
    symbol table or boundary metadata. *)
let rec get_port_name env gr nid pid dir =
  let cs, _ps = gr.symtab in
  let from_cs =
    SM.fold
      (fun _ v acc ->
        if acc <> None then acc
        else if v.val_def = nid && v.def_port = pid then
          Some (sanitize v.val_name)
        else acc)
      cs None
  in
  match from_cs with
  | Some name -> Some name
  | None -> (
      match env.parent_env with
      | Some p_env when nid = 0 && dir = `Out -> (
          match NM.find_opt 0 gr.nmap with
          | Some (Boundary (ins, _, _, _)) -> (
              let reversed_ins = List.rev ins in
              match List.nth_opt reversed_ins pid with
              | Some (sn, sp, _) -> get_port_name p_env p_env.curr_gr sn sp `Out
              | None -> None)
          | _ -> None)
      | _ -> None)

(** [var_name ?tag env gr g n p dir] generates a unique C variable name for an
    IF1 port. *)
let var_name ?(tag = "") env gr g n p dir =
  let base_name =
    match get_port_name env gr n p dir with
    | Some name when name <> "" -> sanitize name
    | _ -> ""
  in
  let d_str = match dir with `In -> "i" | `Out -> "o" in
  if g = 0 && n = 0 && dir = `Out then
    if base_name <> "" then base_name else Printf.sprintf "param_p%d" p
  else
    let computed_tag =
      if tag <> "" then tag
      else if n = 0 then "boundary"
      else
        let label =
          match NM.find_opt n gr.nmap with
          | Some (Simple (_, sym, _, _, _)) ->
              sanitize (String.lowercase_ascii (string_of_node_sym sym))
          | Some (Compound (_, sym, _, pr, _, _)) ->
              List.find_map (function Name nm -> Some (sanitize nm) | _ -> None)
                pr
              |> Option.value ~default:"comp"
          | Some (Literal _) -> "lit"
          | Some (Boundary _) -> "boundary"
          | _ -> "node"
        in
        label
    in
    let prefix = if base_name <> "" then base_name else "v" in
    Printf.sprintf "%s_g%d_%s_n%d_p%d_%s" prefix g computed_tag n p d_str

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

(** [c_type_of_if1_ty tm ty] maps an IF1 type to its corresponding C-AST type. *)
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

(** [type_id_of_if1_ty _tm ty] returns the runtime type ID for a given IF1 type. *)
let type_id_of_if1_ty _tm ty =
  match ty with
  | Basic REAL -> 0
  | Basic DOUBLE -> 1
  | Basic INTEGRAL -> 2
  | Basic BOOLEAN -> 3
  | Array_dv _ | Array_ty _ -> 10
  | _ -> 0

(** [get_expr env g n p dir] recursively resolves an IF1 port to a C expression. *)
let rec get_expr ?(visited = PortSet.empty) env g n p dir =
  if PortSet.mem (g, n, p, dir) visited then
    C.Id (var_name env env.curr_gr g n p dir)
  else
    let visited = PortSet.add (g, n, p, dir) visited in
    match FullPortMap.find_opt (g, n, p, dir) env.var_map with
    | Some e -> e
    | None -> (
        if g <> env.curr_gid then
          match env.parent_env with
          | Some p_env -> get_expr ~visited:PortSet.empty p_env g n p dir
          | None -> C.Id (var_name env env.curr_gr g n p dir)
        else
          match FullPortMap.find_opt (g, n, p, dir) env.preds with
          | Some (sg, sn, sp, sd) -> get_expr ~visited env sg sn sp sd
          | None -> (
              let find_in_parents e sname =
                let match_found =
                  FullPortMap.fold
                    (fun _ expr acc ->
                      if acc <> None then acc
                      else
                        match expr with
                        | C.Id id when id = sname || String.starts_with ~prefix:(sname ^ "_g") id -> Some expr
                        | _ -> acc)
                    e.var_map None
                in
                match match_found with
                | Some res -> Some res
                | None -> (match e.parent_env with Some pe -> None | None -> None)
              in
              let local_boundary_expr =
                if g = env.curr_gid && n = 0 && dir = `Out then
                  let fanout = PortFanout.find_opt (0, p) env.fanout_map |> Option.value ~default:0 in
                  let is_mandatory = env.curr_gid <> 0 || fanout > 1 || PortSet.mem (0, 0, p, `Out) env.mandatory_ports in
                  if is_mandatory then Some (C.Id (var_name env env.curr_gr g n p dir))
                  else match get_port_name env env.curr_gr n p dir with
                       | Some name when name <> "" -> find_in_parents env (sanitize name)
                       | _ -> None
                else None
              in
              match local_boundary_expr with
              | Some expr -> expr
              | None -> (
                  match env.parent_env with
                  | Some p_env -> get_expr ~visited:PortSet.empty p_env g n p dir
                  | None -> (
                      match NM.find_opt n env.curr_gr.nmap with
                      | Some (Literal (_, ty, val_str, _)) -> (
                          match ty with
                          | CHARACTER -> let s = if String.length val_str > 0 then String.sub val_str 0 1 else " " in C.LitInt (int_of_char s.[0])
                          | REAL | DOUBLE -> C.LitFloat (float_of_string val_str)
                          | _ -> (try C.LitInt (int_of_string val_str) with _ -> C.Id val_str))
                      | _ -> C.Id (var_name env env.curr_gr g n p dir)))))

(** [get_port_type env gr nid pid dir] infers the C type for a specific IF1
    port. *)
let rec get_port_type env gr nid pid dir =
  let sname = match get_port_name env gr nid pid dir with | Some n -> sanitize n | None -> "" in
  let is_int_name s = s = "i" || s = "index" || s = "lo" || s = "hi" || s = "count" || s = "n" || String.starts_with ~prefix:"__LFIDX" s || String.starts_with ~prefix:"__LFR" s || String.starts_with ~prefix:"__LFD" s || String.starts_with ~prefix:"__LFMR" s || String.starts_with ~prefix:"__LFTOTAL" s in
  let known_int_node = match NM.find_opt nid gr.nmap with | Some (Simple (_, sym, _, _, _)) -> List.mem sym [RANGEGEN; ALIML; ALIMH; ASIZE; DV_DIMENSION; DV_NUM_RANK; DV_OFFSET_AT] | _ -> false in
  if known_int_node then C.Basic "int32_t"
  else if is_int_name sname then C.Basic "int32_t"
  else if String.starts_with ~prefix:"__LFA" sname then C.Basic "sisal_array_t"
  else
    let ty_id_opt = ES.fold (fun ((sn, sp), (dn, dp), t) acc -> if acc <> None then acc else let match_src = sn = nid && sp = pid && dir = `Out in let match_dst = dn = nid && dp = pid && dir = `In in if (match_src || match_dst) && t <> 0 then Some t else acc) gr.eset None in
    match ty_id_opt with
    | Some tid -> (let basic_opt = match tid with | 1 -> Some BOOLEAN | 3 -> Some CHARACTER | 4 -> Some DOUBLE | 6 -> Some INTEGRAL | 8 -> Some REAL | 2 -> Some BYTE | 5 -> Some HALF | 7 -> Some LONG | 9 -> Some SHORT | 10 -> Some UBYTE | 11 -> Some UCHAR | 12 -> Some UINT | 13 -> Some ULONG | 14 -> Some USHORT | _ -> None in match basic_opt with | Some b -> c_type_of_if1_basic b | None -> (try c_type_of_if1_ty env.tm (TM.find tid env.tm) with _ -> C.Basic "float"))
    | None -> (if nid = 0 && dir = `Out then match env.parent_env with | Some p_env -> (match NM.find_opt 0 gr.nmap with | Some (Boundary (ins, _, _, _)) -> (let reversed_ins = List.rev ins in match List.nth_opt reversed_ins pid with | Some (sn, sp, _) -> get_port_type p_env p_env.curr_gr sn sp `Out | None -> C.Basic "float") | _ -> C.Basic "float") | None -> C.Basic "float"
               else match NM.find_opt nid gr.nmap with
               | Some (Simple (_, (DV_LOAD_LINEAR | DV_ELEMENT | AELEMENT), _, _, _)) -> let is_double = match env.parent_env with | Some p_env -> TM.exists (fun _ ty -> match ty with Basic DOUBLE -> true | _ -> false) p_env.tm | None -> false in if is_double then C.Basic "double" else C.Basic "float"
               | Some (Simple (_, sym, _, _, _)) when List.mem sym [DV_CREATE; DV_RESHAPE; DV_SLICE; DV_PERMUTE; DV_ROTATE; DV_COMPRESS; DV_OUTERPRODUCT; DV_SORT; DV_REVERSE; DV_RESHAPE_BY_SHAPE; DV_GATHER; DV_SCATTER; AGATHER; ASCATTER; ABUILD; AFILL; ACREATE] -> C.Basic "sisal_array_t"
               | Some (Compound (_, sym, _, pr, _, _)) -> let is_forall = List.exists (function Name n -> n = "FORALL" | _ -> false) pr in if (is_forall || sym = STREAM || sym = MAT) && pid = 0 then C.Basic "sisal_array_t" else if is_forall || sym = STREAM || sym = MAT then C.Basic "int32_t" else C.Basic "float"
               | _ -> C.Basic "float")

let rec get_tuple_types tm tid = try match TM.find tid tm with | Tuple_ty (et, next) -> et :: get_tuple_types tm next | _ -> [] with _ -> []
let get_function_param_types tm tid = try match TM.find tid tm with | Function_ty (args_id, _, _) -> get_tuple_types tm args_id | _ -> [] with _ -> []
let get_elem_type env gr nid = let ty_id = ES.fold (fun ((sn, sp), _, t) acc -> if sn = nid && sp = 0 && t <> 0 then Some t else acc) gr.eset None |> Option.value ~default:0 in try match TM.find ty_id env.tm with | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm | _ -> Unknown_ty with _ -> Unknown_ty
let string_of_pragma = function | Name s | Ast_type s | Subscript s -> s | _ -> ""
let rec collect_record_fields tm label = match TM.find_opt label tm with | Some (Record (field_ty_id, next_label, name)) -> let s_name = String.trim name in if s_name = "" || s_name = "UNKNOWN" then collect_record_fields tm next_label else let field_ty_val = try TM.find field_ty_id tm with _ -> Unknown_ty in if field_ty_val = Unknown_ty then collect_record_fields tm next_label else let field_ty = c_type_of_if1_ty tm field_ty_val in (sanitize name, field_ty) :: collect_record_fields tm next_label | _ -> []
let find_subgraph gr name = let target = String.uppercase_ascii name in let res = NM.choose_opt (NM.filter (fun _ n -> match n with | Compound (_, _, _, pr, _, _) -> List.exists (function | Name s | Ast_type s | Subscript s -> String.uppercase_ascii s = target | _ -> false) pr | _ -> false) gr.nmap) in res |> Option.map (fun (id, n) -> match n with Compound (_, _, _, _, g, _) -> (id, g) | _ -> assert false)
let get_subgraph_errors env gid cid = match NM.find_opt cid env.curr_gr.nmap with | Some (Compound (sub_cid, _, _, _, sub_gr, _)) -> (let sub_gid = alloc_gid env.gid_table gid sub_cid in match NM.find_opt 0 sub_gr.nmap with | Some (Boundary (_, outs, errs, _)) -> List.mapi (fun i _ -> let pid = List.length outs + i in get_expr env sub_gid 0 pid `Out) errs | _ -> []) | _ -> []
let find_boundary_selects gr = ES.fold (fun ((sn, _sp), (dn, dp), _) acc -> if dn = 0 then match NM.find_opt sn gr.nmap with | Some (Simple (_, SELECT, _, _, _)) -> (sn, dp) :: acc | _ -> acc else acc) gr.eset []
let topo_sort gr = let nodes = NM.bindings gr.nmap |> List.map fst in let in_degree = List.fold_left (fun m id -> IntMap.add id 0 m) IntMap.empty nodes in let adj_list = List.fold_left (fun m id -> IntMap.add id [] m) IntMap.empty nodes in let in_degree, adj_list = ES.fold (fun ((sn, _), (dn, _), _) (deg, adj) -> if sn <> 0 && IntMap.mem dn deg && IntMap.mem sn adj then (IntMap.add dn (IntMap.find dn deg + 1) deg, IntMap.add sn (dn :: IntMap.find sn adj) adj) else (deg, adj)) gr.eset (in_degree, adj_list) in let worklist = List.filter (fun id -> IntMap.find id in_degree = 0) nodes in let rec loop worklist acc in_degree = match worklist with | [] -> List.rev acc | n :: rest -> let succs = IntMap.find n adj_list in let new_work, in_degree' = List.fold_left (fun (wl, deg) dn -> let d = IntMap.find dn deg - 1 in let deg' = IntMap.add dn d deg in if d = 0 then (dn :: wl, deg') else (wl, deg')) ([], in_degree) succs in loop (rest @ new_work) (n :: acc) in_degree' in let sorted = loop worklist [] in_degree in let num_nodes = List.length nodes in if List.length sorted < num_nodes then let sorted_set = List.fold_left (fun s id -> IntSet.add id s) IntSet.empty sorted in sorted @ List.filter (fun id -> not (IntSet.mem id sorted_set)) nodes else sorted
let compute_fanout gr = let counts = ES.fold (fun ((sn, sp), _, _) m -> let count = PortFanout.find_opt (sn, sp) m |> Option.value ~default:0 in PortFanout.add (sn, sp) (count + 1) m) gr.eset PortFanout.empty in let mandatory = ES.fold (fun ((sn, sp), (dn, dp), _) s -> let needs_var = match NM.find_opt dn gr.nmap with | Some (Simple (_, (RELEMENTS | RREPLACE), _, _, _)) -> dp = 1 || dp = 0 | Some (Simple (_, (DV_ELEMENT | AELEMENT | ASIZE | DV_DIMENSION | ALIML | ALIMH | AISEMPTY | DV_LOAD_LINEAR), _, _, _)) -> dp = 0 | Some (Compound _) -> true | _ -> false in if needs_var then PortSet.add (0, sn, sp, `Out) s else s) gr.eset PortSet.empty in (counts, mandatory)
