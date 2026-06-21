(** apple_helpers.ml: Utility functions for IF1 to C-AST lowering on Apple
    Silicon. Provides helpers for name sanitization, type mapping, and IF1
    traversal. *)

open Ir.If1
open Apple_env

(** [c_op_of_sym sym] maps an IF1 node symbol to a C binary operator. *)
let c_op_of_sym = function
  | ADD -> Some C.Add
  | SUBTRACT -> Some C.Sub
  | TIMES -> Some C.Mul
  | FDIVIDE | IDIVIDE -> Some C.Div
  | EQUAL -> Some C.Eq
  | LESSER -> Some C.Lt
  | LESSER_EQUAL -> Some C.Le
  | GREATER -> Some C.Gt
  | GREATER_EQUAL -> Some C.Ge
  | AND -> Some C.LogAnd
  | OR -> Some C.LogOr
  | SHL -> Some C.Shl
  | SHR | ASHR -> Some C.Shr
  | BITAND -> Some C.BitAnd
  | BITOR -> Some C.BitOr
  | BITXOR -> Some C.BitXor
  | _ -> None

(** [sanitize name] removes illegal characters from a Sisal name for C
    compatibility. *)
let sanitize name =
  let s =
    String.map
      (fun c ->
        match c with
        | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c
        | _ -> '_')
      name
  in
  if String.length s > 0 && s.[0] >= '0' && s.[0] <= '9' then "_" ^ s else s

(** [fresh_name env base] -> a readable, unique C identifier from [base].
    Sanitizes [base]; if it is already taken (env.seen_decls), it finds a
    trailing number and increments it (e.g. "lb" -> "lb1" -> "lb2", "x3" -> "x4")
    until there is no collision; otherwise it appends a number. The returned env
    records the chosen name so later calls stay unique. (Same idea LLVM uses to
    uniquify value names.) Hand every minted temp through this so no name can
    shadow a parameter, a user variable, or another temp. *)
let fresh_name env base =
  let s = match sanitize base with "" -> "_t" | s -> s in
  if not (StringSet.mem s env.seen_decls) then
    (s, { env with seen_decls = StringSet.add s env.seen_decls })
  else begin
    (* split off any trailing digits: "lb" -> ("lb", 1); "x3" -> ("x", 4) *)
    let n = String.length s in
    let i = ref n in
    while !i > 0 && s.[!i - 1] >= '0' && s.[!i - 1] <= '9' do decr i done;
    let stem = String.sub s 0 !i in
    let start =
      if !i < n then (try int_of_string (String.sub s !i (n - !i)) + 1 with _ -> 1)
      else 1
    in
    let rec pick k =
      let cand = stem ^ string_of_int k in
      if StringSet.mem cand env.seen_decls then pick (k + 1) else cand
    in
    let name = pick start in
    (name, { env with seen_decls = StringSet.add name env.seen_decls })
  end

(** [get_port_name env gr nid pid dir] finds a descriptive name for a port. *)
let get_port_name _env gr nid pid dir =
  let cs, _ps = gr.symtab in
  SM.fold (fun raw_name v acc ->
    if acc <> None then acc
    else if v.val_def = nid && v.def_port = pid then
      if nid = 0 && dir <> `Out then acc (* Boundary inputs (In) don't get these names *)
      else Some (sanitize v.val_name)
    else acc) cs None

(** [get_port_name_from_cs gr nid pid dir] looks up a port's name in the graph's symtab. *)
let get_port_name_from_cs gr nid pid dir = get_port_name () gr nid pid dir

(** [scope_of gid_name_map gid] returns a unique scope prefix for a GID.
    The GID is always appended to guarantee uniqueness when multiple scopes
    share the same human-readable name (e.g. two PREDICATE sub-graphs). *)
let scope_of gid_name_map gid =
  match IntMap.find_opt gid gid_name_map with
  | Some name -> Printf.sprintf "%s_%d" name gid
  | None -> "g" ^ string_of_int gid

(** [var_name gid_name_map gid nid pid dir] generates a unique C variable name for an IF1 port. *)
let var_name gid_name_map gid nid pid dir =
  let d_str = match dir with `In -> "i" | `Out -> "o" in
  Printf.sprintf "v_%s_n__%d_p%d_%s" (scope_of gid_name_map gid) nid pid d_str

let get_c_name proc_map gid_name_map gid nid pid dir gr =
  if gid = 0 && IntMap.mem nid proc_map then
    IntMap.find nid proc_map
  else
    match get_port_name_from_cs gr nid pid dir with
    | Some name -> Printf.sprintf "v_%s_n__%d_%s" (scope_of gid_name_map gid) nid (sanitize name)
    | None -> var_name gid_name_map gid nid pid dir

(** [get_expr env gid nid pid dir] resolves a port to its C identifier. *)
let get_expr env gid nid pid dir =
  match FullPortMap.find_opt (gid, nid, pid, dir) env.var_map with
  | Some expr -> expr
  | None ->
      (* Literals are never in var_map but can be resolved directly *)
      match NM.find_opt nid env.curr_gr.nmap with
      | Some (Literal (_, code, value, _)) ->
          (match code with
           | REAL | DOUBLE -> C.LitFloat (float_of_string value)
           | BOOLEAN -> C.Id (String.lowercase_ascii value)
           | _ -> try C.LitInt (int_of_string value) with _ -> C.LitInt 0)
      | _ ->
          let name = get_c_name env.proc_map env.gid_name_map gid nid pid dir env.curr_gr in
          C.Id name

(** [c_type_of_if1_basic b] maps a basic IF1 scalar type to a C type string. *)
let c_type_of_if1_basic = function
  | BOOLEAN -> C.Basic "bool"
  | CHARACTER | UCHAR -> C.Basic "char"
  | DOUBLE -> C.Basic "double"
  | REAL -> C.Basic "float"
  | INTEGRAL | BYTE | UBYTE -> C.Basic "int32_t"
  | LONG | ULONG -> C.Basic "int64_t"
  | SHORT | USHORT -> C.Basic "int16_t"
  | UINT -> C.Basic "uint32_t"
  | _ -> C.Basic "float"

(** [c_type_of_if1_ty tm ty] maps an IF1 type to its corresponding C-AST type. *)
let c_type_of_if1_ty tm ty =
  match ty with
  | Basic b -> c_type_of_if1_basic b
  | Array_dv _ | Array_ty _ -> C.Basic "sisal_array_t"
  | Record (id, _, name) ->
      let sname = String.lowercase_ascii name in
      if sname = "int" || sname = "integer" || sname = "int32" then C.Basic "int32_t"
      else if sname = "double" || sname = "double_real" then C.Basic "double"
      else if sname = "float" || sname = "real" then C.Basic "float"
      else if sname = "bool" || sname = "boolean" then C.Basic "bool"
      else if id <= 12 then (
        match id with
        | 1 -> C.Basic "bool" | 3 -> C.Basic "char" | 4 | 5 -> C.Basic "double"
        | 6 -> C.Basic "int32_t" | 7 -> C.Basic "int64_t" | 8 -> C.Basic "float"
        | 12 -> C.Basic "uint32_t" | _ -> C.Basic "sisal_array_t"
      ) else C.Basic (Printf.sprintf "struct struct_rec_%d" id)
  | _ -> C.Basic "sisal_array_t"

(** [get_compound_type pragma_list] identifies the specific compound node variant. *)
let get_compound_type pr =
  List.find_map (function Compound_of c -> Some c | _ -> None) pr |> Option.value ~default:If1_Unknown

(** [find_subgraph gr role_name] searches for a specific subgraph within a compound node. *)
let find_subgraph gr target =
  let role_target = match target with
    | "PREDICATE" -> Some If1_predicate
    | "THEN" -> Some If1_then
    | "ELSE" -> Some If1_else
    | "GENERATOR" -> Some If1_generator
    | "BODY" -> Some If1_body
    | "RETURNS" | "RETURN" -> Some If1_results
    | "INIT" -> Some If1_loop_initial
    | "TEST" -> Some If1_loop_test
    | _ -> None in
  let res = NM.choose_opt (NM.filter (fun _ n -> 
    match n with 
    | Compound (_, _, _, pr, _, _) -> 
        let has_role = match role_target with
         | Some r -> get_compound_type pr = r
         | None -> false in
        has_role
    | _ -> false) gr.nmap) in 
  res |> Option.map (fun (id, n) -> match n with Compound (_, _, _, _, g, _) -> (id, g) | _ -> assert false)

(** [get_graph_by_gid env target_gid] searches the graph hierarchy. *)
let get_graph_by_gid env target_gid =
  match IntMap.find_opt target_gid env.procedures_info with
  | Some g -> g
  | None ->
      let rec find_in_gr g cur_gid =
        if cur_gid = target_gid then Some g
        else NM.fold (fun nid node acc ->
          if acc <> None then acc
          else match node with
            | Compound (_, _, _, _, sub_gr, _) ->
                let sub_gid = try GidMap.find (cur_gid, nid) env.gid_table with _ -> -1 in
                find_in_gr sub_gr sub_gid
            | _ -> None
          ) g.nmap None in
      match find_in_gr env.curr_gr env.curr_gid with
      | Some g -> g
      | None -> env.curr_gr

(** [topo_sort gr] returns a list of node IDs in dependency order. *)
let topo_sort gr =
  let nodes = NM.bindings gr.nmap |> List.map fst |> List.filter (fun id -> id <> 0) in
  let rec visit visited stack id =
    if IntSet.mem id visited then (visited, stack)
    else
      let deps = ES.fold (fun ((sn, _), (dn, _), _) acc -> if dn = id && sn <> 0 then IntSet.add sn acc else acc) gr.eset IntSet.empty in
      let visited, stack = IntSet.fold (fun dep (v, s) -> visit v s dep) deps (IntSet.add id visited, stack) in
      (visited, id :: stack) in
  let _, sorted = List.fold_left (fun (v, s) id -> visit v s id) (IntSet.empty, []) nodes in
  let sorted = List.rev sorted in
  let num_nodes = List.length nodes in if List.length sorted < num_nodes then let sorted_set = List.fold_left (fun s id -> IntSet.add id s) IntSet.empty sorted in sorted @ List.filter (fun id -> not (IntSet.mem id sorted_set)) nodes else sorted

(** [topo_sort_edges gr] returns the graph's edges in data-dependence order.
    Node 0 (the boundary = graph inputs) comes first, then the nodes in
    [topo_sort] order; for each node we emit its OUTGOING edges (tail = node).
    An edge's tail value is ready once that node's own inputs are done, so this
    walk yields every edge after the edges that feed its tail. *)
let topo_sort_edges gr =
  let node_order = 0 :: topo_sort gr in
  List.concat_map (fun nid ->
    ES.fold (fun e acc -> let ((sn, _), _, _) = e in if sn = nid then e :: acc else acc)
      gr.eset []
    |> List.sort compare)
    node_order

let get_function_param_types tm ty_id =
  match TM.find_opt ty_id tm with
  | Some (Function_ty (ins, _, _)) ->
      let rec flatten label =
        if label = 0 then []
        else match TM.find_opt label tm with
          | Some (Tuple_ty (curr, next)) -> curr :: flatten next
          | _ -> [label] in
      flatten ins
  | _ -> []

let get_elem_type env gr nid =
  let ty_id = ES.fold (fun ((sn, sp), _, t) acc -> if sn = nid && sp = 0 && t <> 0 then Some t else acc) gr.eset None |> Option.value ~default:0 in
  let tm = get_typemap_tm gr in
  try match TM.find ty_id tm with | Array_dv et_id | Array_ty et_id -> TM.find et_id tm | _ -> Unknown_ty with _ -> Unknown_ty

let rec collect_record_fields tm label =
  match TM.find_opt label tm with
  | Some (Record (field_ty_id, next_label, name)) ->
      let ty = c_type_of_if1_ty tm (try TM.find field_ty_id tm with _ -> Basic REAL) in
      let fields = [ (name, ty) ] in
      fields @ collect_record_fields tm next_label
  | _ -> []

let boundary_in_port_count gr = match NM.find_opt 0 gr.nmap with | Some (Boundary (ins, _, _, _)) -> List.length ins | _ -> 0
let boundary_out_port_count gr = match NM.find_opt 0 gr.nmap with | Some (Boundary (_, outs, _, _)) -> List.length outs | _ -> 0
