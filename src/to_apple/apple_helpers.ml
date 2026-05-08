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
  let cs, ps = gr.symtab in
  let search_map m =
    SM.fold (fun _ v acc ->
      if acc <> None then acc
      else if v.val_def = nid && v.def_port = pid then
        if nid = 0 && dir <> `Out then acc
        else Some (sanitize v.val_name)
      else acc) m None in
  match search_map cs with
  | Some name -> Some name
  | None ->
      match search_map ps with
      | Some name -> Some name
      | None ->
          match env.parent_env with
          | Some p_env when nid = 0 && dir = `Out ->
              (* Boundary input port: resolve name via parent graph's edge set. *)
              let cid = env.compound_nid_in_parent in
              let feeding = all_edges_ending_at_port cid pid p_env.curr_gr in
              (match ES.choose_opt feeding with
               | Some ((src_n, src_p), _, _) ->
                   get_port_name p_env p_env.curr_gr src_n src_p `Out
               | None -> None)
          | _ -> None

(** [get_port_name_from_cs gr nid pid dir] looks up a port's name ONLY in the
    local symbol table (cs). This avoids name leaking from parent scopes. *)
let get_port_name_from_cs gr nid pid dir =
  let cs, _ps = gr.symtab in
  SM.fold (fun _ v acc ->
    if acc <> None then acc
    else if v.val_def = nid && v.def_port = pid then
      if nid = 0 && dir <> `Out then acc
      else Some (sanitize v.val_name)
    else acc) cs None

(** [var_name ?tag env gr g n p dir] generates a unique C variable name for an
    IF1 port. *)
let var_name ?(tag = "") env gr g n p dir =
  let base_name =
    match get_port_name env gr n p dir with
    | Some name when name <> "" -> sanitize name
    | _ -> ""
  in
  let d_str = match dir with `In -> "i" | `Out -> "o" in
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
    Some (C.Id (var_name env env.curr_gr g n p dir))
  else
    let visited = PortSet.add (g, n, p, dir) visited in
    match FullPortMap.find_opt (g, n, p, dir) env.var_map with
    | Some e -> Some e
    | None -> (
        if g <> env.curr_gid then
          match env.parent_env with
          | Some p_env -> get_expr ~visited:PortSet.empty p_env g n p dir
          | None -> None
        else
          match FullPortMap.find_opt (g, n, p, dir) env.preds with
          | Some (sg, sn, sp, sd) -> get_expr ~visited env sg sn sp sd
          | None -> (
              if g = env.curr_gid && n = 0 && dir = `Out then
                (* Boundary input port: resolve via parent graph's edge set. *)
                match env.parent_env with
                | Some p_env ->
                    let cid = env.compound_nid_in_parent in
                    let feeding = all_edges_ending_at_port cid p p_env.curr_gr in
                    (match ES.choose_opt feeding with
                     | Some ((src_n, src_p), _, _) ->
                         get_expr ~visited:PortSet.empty p_env p_env.curr_gid
                           src_n src_p `Out
                     | None -> None)
                | None -> None
              else
                match NM.find_opt n env.curr_gr.nmap with
                | Some (Literal (_, ty, val_str, _)) -> (
                    match ty with
                    | CHARACTER ->
                        let s =
                          if String.length val_str > 0 then
                            String.sub val_str 0 1
                          else " "
                        in
                        Some (C.LitInt (int_of_char s.[0]))
                    | REAL | DOUBLE -> Some (C.LitFloat (float_of_string val_str))
                    | _ -> (
                        try Some (C.LitInt (int_of_string val_str))
                        with _ -> Some (C.Id val_str)))
                | _ -> (
                    (* Final fallback: try parents by name if it's a known symbol.
                       Match exact name OR names of the form <name>_g<N>_... which are
                       the generated var names for boundary/computed ports with that
                       symbol name. FullPortMap.fold goes ascending by (gid,...) so
                       the earliest-scope (lowest-gid) entry is found first. *)
                    match env.parent_env with
                    | Some p_env -> (
                        match get_port_name env env.curr_gr n p dir with
                        | Some name when name <> "" ->
                            let prefix = name ^ "_g" in
                            let plen = String.length prefix in
                            let rec find_name e s =
                              FullPortMap.fold (fun _ expr acc ->
                                if acc <> None then acc
                                else match expr with
                                     | C.Id id when id = s ||
                                         (String.length id >= plen &&
                                          String.sub id 0 plen = prefix) -> Some expr
                                     | _ -> acc
                              ) e.var_map None
                              |> (function
                                  | Some x -> Some x
                                  | None -> (match e.parent_env with Some pe -> find_name pe s | None -> None))
                            in
                            find_name p_env name
                        | _ -> None)
                    | None -> None)))

(** [get_port_type env gr nid pid dir] infers the C type for a specific IF1
    port. *)
let rec get_port_type env gr nid pid dir =
  let _, tm, _ = gr.typemap in
  let ty_id_opt = 
    ES.fold (fun ((sn, sp), (dn, dp), t) acc -> 
      if acc <> None then acc 
      else 
        let match_src = (sn = nid && sp = pid && dir = `Out) in
        let match_dst = (dn = nid && dp = pid && dir = `In) in
        if (match_src || match_dst) && t <> 0 then Some t else acc
    ) gr.eset None 
  in
  match ty_id_opt with
  | Some tid -> (
      try 
        let if1_ty = TM.find tid tm in
        c_type_of_if1_ty tm if1_ty
      with _ -> C.Basic "float")
  | None -> (
      (* Fallback heuristics for ports without explicit edge types *)
      let sname = match get_port_name env gr nid pid dir with | Some n -> sanitize n | None -> "" in
      let is_int_name s = s = "i" || s = "index" || s = "lo" || s = "hi" || s = "count" || s = "n" || String.starts_with ~prefix:"__LFIDX" s || String.starts_with ~prefix:"__LFR" s || String.starts_with ~prefix:"__LFD" s || String.starts_with ~prefix:"__LFMR" s || String.starts_with ~prefix:"__LFTOTAL" s in
      let known_int_node = match NM.find_opt nid gr.nmap with | Some (Simple (_, sym, _, _, _)) -> List.mem sym [RANGEGEN; ALIML; ALIMH; ASIZE; DV_DIMENSION; DV_NUM_RANK; DV_OFFSET_AT] | _ -> false in
      if known_int_node then C.Basic "int32_t"
      else if is_int_name sname then C.Basic "int32_t"
      else if String.starts_with ~prefix:"__LFA" sname || String.starts_with ~prefix:"__LFB" sname || String.starts_with ~prefix:"__LFSH" sname then C.Basic "sisal_array_t"
      else if nid = 0 && dir = `Out then (
        match env.parent_env with
        | Some p_env ->
            let cid = env.compound_nid_in_parent in
            let feeding = all_edges_ending_at_port cid pid p_env.curr_gr in
            (match ES.choose_opt feeding with
             | Some ((src_n, src_p), _, _) ->
                 get_port_type p_env p_env.curr_gr src_n src_p `Out
             | None -> C.Basic "float")
        | None -> C.Basic "float")
      else match NM.find_opt nid gr.nmap with
      | Some (Simple (_, (DV_LOAD_LINEAR | DV_ELEMENT | AELEMENT), _, _, _)) -> 
          let is_double = match env.parent_env with 
                          | Some p_env -> TM.exists (fun _ ty -> match ty with Basic DOUBLE -> true | _ -> false) p_env.tm 
                          | None -> TM.exists (fun _ ty -> match ty with Basic DOUBLE -> true | _ -> false) env.tm
          in if is_double then C.Basic "double" else C.Basic "float"
      | Some (Simple (_, sym, _, _, _)) when List.mem sym [DV_CREATE; DV_RESHAPE; DV_SLICE; DV_PERMUTE; DV_ROTATE; DV_COMPRESS; DV_OUTERPRODUCT; DV_SORT; DV_REVERSE; DV_RESHAPE_BY_SHAPE; DV_GATHER; DV_SCATTER; AGATHER; ASCATTER; ABUILD; AFILL; ACREATE] -> C.Basic "sisal_array_t"
      | Some (Compound (_, sym, _, pr, _, _)) -> 
          let is_forall = List.exists (function Name n -> n = "FORALL" | _ -> false) pr in 
          if (is_forall || sym = STREAM || sym = MAT) && pid = 0 then C.Basic "sisal_array_t" 
          else if is_forall || sym = STREAM || sym = MAT then C.Basic "int32_t" 
          else C.Basic "float"
      | _ -> C.Basic "float")

let rec get_tuple_types tm tid = try match TM.find tid tm with | Tuple_ty (et, next) -> et :: get_tuple_types tm next | _ -> [] with _ -> []
let get_function_param_types tm tid = try match TM.find tid tm with | Function_ty (args_id, _, _) -> get_tuple_types tm args_id | _ -> [] with _ -> []
let get_elem_type env gr nid = let ty_id = ES.fold (fun ((sn, sp), _, t) acc -> if sn = nid && sp = 0 && t <> 0 then Some t else acc) gr.eset None |> Option.value ~default:0 in try match TM.find ty_id env.tm with | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm | _ -> Unknown_ty with _ -> Unknown_ty
let string_of_pragma = function | Name s | Ast_type s | Subscript s -> s | _ -> ""
let rec collect_record_fields tm label = match TM.find_opt label tm with | Some (Record (field_ty_id, next_label, name)) -> let s_name = String.trim name in if s_name = "" || s_name = "UNKNOWN" then collect_record_fields tm next_label else let field_ty_val = try TM.find field_ty_id tm with _ -> Unknown_ty in if field_ty_val = Unknown_ty then collect_record_fields tm next_label else let field_ty = c_type_of_if1_ty tm field_ty_val in (sanitize name, field_ty) :: collect_record_fields tm next_label | _ -> []
let find_subgraph gr name = let target = String.uppercase_ascii name in let res = NM.choose_opt (NM.filter (fun _ n -> match n with | Compound (_, _, _, pr, _, _) -> List.exists (function | Name s | Ast_type s | Subscript s -> String.uppercase_ascii s = target | _ -> false) pr | _ -> false) gr.nmap) in res |> Option.map (fun (id, n) -> match n with Compound (_, _, _, _, g, _) -> (id, g) | _ -> assert false)
let get_subgraph_errors env gid cid = match NM.find_opt cid env.curr_gr.nmap with | Some (Compound (sub_cid, _, _, _, sub_gr, _)) -> (let sub_gid = alloc_gid env.gid_table gid sub_cid in match NM.find_opt 0 sub_gr.nmap with | Some (Boundary (_, outs, errs, _)) -> List.mapi (fun i _ -> let pid = List.length outs + i in get_expr env sub_gid 0 pid `Out) errs | _ -> []) | _ -> []
(* [assert_compound_boundary_types gr] checks that for every edge
   (sn,sp) -> (dn,dp) in gr where dn is a Compound, every edge
   (0,dp) -> (*,*) inside that compound's subgraph carries the same
   type id.  Type id 0 means "unknown" and is skipped. *)
let assert_compound_boundary_types gr =
  ES.iter (fun ((sn, sp), (dn, dp), outer_ty) ->
    if outer_ty = 0 then ()
    else
      match NM.find_opt dn gr.nmap with
      | Some (Compound (_, _, _, _, sub_gr, _)) ->
          ES.iter (fun ((ssn, ssp), (dsn, dsp), inner_ty) ->
            if ssn = 0 && ssp = dp && inner_ty <> 0 && inner_ty <> outer_ty then begin
              Printf.eprintf
                "[assert] TYPE MISMATCH at compound boundary:\n\
                \  outer: %d:%d -> %d:%d  ty=%d\n\
                \  inner: 0:%d -> %d:%d  ty=%d\n%!"
                sn sp dn dp outer_ty
                dp dsn dsp inner_ty;
              assert false
            end
          ) sub_gr.eset
      | _ -> ()
  ) gr.eset

let find_boundary_selects gr =ES.fold (fun ((sn, _sp), (dn, dp), _) acc -> if dn = 0 then match NM.find_opt sn gr.nmap with | Some (Simple (_, SELECT, _, _, _)) -> (sn, dp) :: acc | _ -> acc else acc) gr.eset []
(* [print_topo_order env ~label gid gr] prints the symbol table, proposed C
   declarations for cs vars, then the topological sort of [gr] to stderr.
   Prints recursively because lower_graph calls this at entry for every subgraph. *)
let print_topo_order env ?(label = "") gid gr =
  (* --- symtab dump -------------------------------------------------------- *)
  let cs, ps = gr.symtab in
  let prefix = if label = "" then "" else label ^ " " in
  Printf.eprintf "[symtab] %sgid=%d\n%!" prefix gid;
  let print_sym_map tag m =
    if SM.is_empty m then
      Printf.eprintf "  %s: (empty)\n%!" tag
    else begin
      Printf.eprintf "  %s:\n%!" tag;
      SM.iter (fun name v ->
        Printf.eprintf "    %-24s  n%d:p%d  ty=%d\n%!"
          (sanitize name) v.val_def v.def_port v.val_ty) m
    end
  in
  print_sym_map "LOCAL-SYM (cs)" cs;
  print_sym_map "GLOBAL-SYM (ps)" ps;
  (* --- proposed C declarations from cs vars --------------------------------
     For each cs entry where val_def != 0 (i.e. computed by a node in this
     graph, not a boundary input) and the type isn't a function/unknown,
     show what `T name;` would be emitted. *)
  let _, tm, _ = gr.typemap in
  let is_var_ty ty_id =
    match TM.find_opt ty_id tm with
    | None -> false
    | Some (Function_ty _ | Unknown_ty) -> false
    | Some _ -> true
  in
  let var_decls =
    SM.fold (fun raw_name v acc ->
      if v.val_def = 0 then acc           (* boundary input — skip *)
      else if not (is_var_ty v.val_ty) then acc
      else
        let sname = sanitize raw_name in
        let ty = get_port_type env gr v.val_def v.def_port `Out in
        (v.def_port, sname, ty) :: acc)
      cs []
    |> List.sort_uniq compare
  in
  if var_decls <> [] then begin
    Printf.eprintf "  proposed cs-var decls:\n%!";
    List.iter (fun (_, name, ty) ->
      let ty_str = match ty with
        | C.Basic s -> s
        | C.Pointer (C.Basic s, _) -> s ^ "*"
        | _ -> "?"
      in
      Printf.eprintf "    %s %s;\n%!" ty_str name
    ) var_decls
  end;
  (* --- topo sort (inlined so it precedes the topo_sort definition) -------- *)
  let sorted =
    let nodes = NM.bindings gr.nmap |> List.map fst in
    let in_degree = List.fold_left (fun m id -> IntMap.add id 0 m) IntMap.empty nodes in
    let adj_list  = List.fold_left (fun m id -> IntMap.add id [] m) IntMap.empty nodes in
    let in_degree, adj_list =
      ES.fold (fun ((sn, _), (dn, _), _) (deg, adj) ->
        if sn <> 0 && IntMap.mem dn deg && IntMap.mem sn adj
        then (IntMap.add dn (IntMap.find dn deg + 1) deg,
              IntMap.add sn (dn :: IntMap.find sn adj) adj)
        else (deg, adj))
        gr.eset (in_degree, adj_list)
    in
    let worklist = List.filter (fun id -> IntMap.find id in_degree = 0) nodes in
    let rec loop wl acc deg =
      match wl with
      | [] -> List.rev acc
      | n :: rest ->
          let new_work, deg' =
            List.fold_left (fun (wl2, d) dn ->
              let d' = IntMap.add dn (IntMap.find dn d - 1) d in
              if IntMap.find dn d' = 0 then (dn :: wl2, d') else (wl2, d'))
              ([], deg) (IntMap.find n adj_list)
          in
          loop (rest @ new_work) (n :: acc) deg'
    in
    loop worklist [] in_degree
  in
  Printf.eprintf "[topo] %sgid=%d  (%d nodes)\n%!" prefix gid (List.length sorted);
  List.iter (fun nid ->
    let desc = match NM.find_opt nid gr.nmap with
      | None -> "???"
      | Some (Boundary _) -> "BOUNDARY"
      | Some (Literal (_, _, v, _)) -> Printf.sprintf "Literal(%s)" v
      | Some (Simple (_, sym, _, _, _)) -> string_of_node_sym sym
      | Some (Compound (_, _, _, pr, _, _)) ->
          let names = List.filter_map (function Name s -> Some s | _ -> None) pr in
          "Compound(" ^ String.concat "," names ^ ")"
      | Some Unknown_node -> "Unknown"
    in
    let port_names =
      List.sort_uniq compare
        (SM.fold (fun name v acc ->
           if v.val_def = nid then (v.def_port, sanitize name) :: acc else acc)
           (SM.union (fun _ a _ -> Some a) cs ps) [])
    in
    let ports_str = match port_names with
      | [] -> ""
      | pns -> "  [" ^ String.concat ", "
                 (List.map (fun (p, n) -> Printf.sprintf "p%d=%s" p n) pns) ^ "]"
    in
    Printf.eprintf "  n%-4d  %s%s\n%!" nid desc ports_str
  ) sorted

let topo_sort gr =let nodes = NM.bindings gr.nmap |> List.map fst in let in_degree = List.fold_left (fun m id -> IntMap.add id 0 m) IntMap.empty nodes in let adj_list = List.fold_left (fun m id -> IntMap.add id [] m) IntMap.empty nodes in let in_degree, adj_list = ES.fold (fun ((sn, _), (dn, _), _) (deg, adj) -> if sn <> 0 && IntMap.mem dn deg && IntMap.mem sn adj then (IntMap.add dn (IntMap.find dn deg + 1) deg, IntMap.add sn (dn :: IntMap.find sn adj) adj) else (deg, adj)) gr.eset (in_degree, adj_list) in let worklist = List.filter (fun id -> IntMap.find id in_degree = 0) nodes in let rec loop worklist acc in_degree = match worklist with | [] -> List.rev acc | n :: rest -> let succs = IntMap.find n adj_list in let new_work, in_degree' = List.fold_left (fun (wl, deg) dn -> let d = IntMap.find dn deg - 1 in let deg' = IntMap.add dn d deg in if d = 0 then (dn :: wl, deg') else (wl, deg')) ([], in_degree) succs in loop (rest @ new_work) (n :: acc) in_degree' in let sorted = loop worklist [] in_degree in let num_nodes = List.length nodes in if List.length sorted < num_nodes then let sorted_set = List.fold_left (fun s id -> IntSet.add id s) IntSet.empty sorted in sorted @ List.filter (fun id -> not (IntSet.mem id sorted_set)) nodes else sorted
let compute_fanout gr = let counts = ES.fold (fun ((sn, sp), _, _) m -> let count = PortFanout.find_opt (sn, sp) m |> Option.value ~default:0 in PortFanout.add (sn, sp) (count + 1) m) gr.eset PortFanout.empty in let mandatory = ES.fold (fun ((sn, sp), (dn, dp), _) s -> let needs_var = match NM.find_opt dn gr.nmap with | Some (Simple (_, (RELEMENTS | RREPLACE), _, _, _)) -> dp = 1 || dp = 0 | Some (Simple (_, (DV_ELEMENT | AELEMENT | ASIZE | DV_DIMENSION | ALIML | ALIMH | AISEMPTY | DV_LOAD_LINEAR), _, _, _)) -> dp = 0 | Some (Compound _) -> true | _ -> false in if needs_var then PortSet.add (0, sn, sp, `Out) s else s) gr.eset PortSet.empty in (counts, mandatory)
