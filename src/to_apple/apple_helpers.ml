open Ir.If1
open Apple_env

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

let var_name g n p dir =
  let d_str = match dir with `In -> "i" | `Out -> "o" in
  Printf.sprintf "v_g%d_n%d_p%d_%s" g n p d_str

let get_port_name gr nid pid _dir =
  let cs, _ps = gr.symtab in
  SM.fold (fun _ v acc ->
    if acc <> None then acc
    else if v.val_def = nid && v.def_port = pid then Some (sanitize v.val_name)
    else acc
  ) cs None

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

let c_type_of_if1_ty tm = function
  | Basic b -> c_type_of_if1_basic b
  | Array_dv _ | Array_ty _ -> C.Basic "sisal_array_t"
  | Record (id, _, _) -> C.Basic ("struct struct_rec_" ^ string_of_int id)
  | Union (id, _, _) -> C.Basic ("union union_un_" ^ string_of_int id)
  | _ -> C.Basic "float"

let type_id_of_if1_ty _tm ty =
  match ty with
  | Basic REAL -> 0
  | Basic DOUBLE -> 1
  | Basic INTEGRAL -> 2
  | Basic BOOLEAN -> 3
  | Array_dv _ | Array_ty _ -> 10
  | _ -> 0

let rec get_expr ?(visited=PortSet.empty) env g n p dir =
  if PortSet.mem (g, n, p, dir) visited then C.Id (var_name g n p dir) else
  let visited = PortSet.add (g, n, p, dir) visited in
  match FullPortMap.find_opt (g, n, p, dir) env.var_map with
  | Some e -> e
  | None ->
      match FullPortMap.find_opt (g, n, p, dir) env.preds with
      | Some (sg, sn, sp, sd) -> get_expr ~visited env sg sn sp sd
      | None ->
          match env.parent_env with
          | Some p_env -> get_expr ~visited p_env g n p dir
          | None -> C.Id (var_name g n p dir)

let get_port_type env gr nid pid dir =
  let ty_id = ES.fold (fun ((sn, sp), (dn, dp), t) acc ->
    let match_src = (sn = nid && sp = pid && dir = `Out) in
    let match_dst = (dn = nid && dp = pid && dir = `In) in
    if (match_src || match_dst) && t <> 0 then Some t else acc
  ) gr.eset None |> Option.value ~default:0 in
  (* For function-body boundary Out ports the outer edge set may be empty
     (LET_NON_REC captures its inputs implicitly).  Fall back to searching
     compound children's inner graphs for an edge from node-0 at this port. *)
  let ty_id =
    if ty_id <> 0 then ty_id
    else if nid = 0 && dir = `Out then
      NM.fold (fun _ node acc ->
        if acc <> 0 then acc
        else match node with
          | Compound (_, _, _, _, sg, _) ->
              ES.fold (fun ((sn, sp), _, t) a ->
                if sn = 0 && sp = pid && t <> 0 then t else a) sg.eset 0
          | _ -> 0
      ) gr.nmap 0
    else ty_id
  in
  try
    let if1_ty = TM.find ty_id env.tm in
    c_type_of_if1_ty env.tm if1_ty
  with _ ->
    match NM.find_opt nid gr.nmap with
    | Some (Boundary (ins, _outs, _, _)) ->
        if nid = 0 && dir = `Out then
          let ty_id = List.find_map (fun (t, p, _) -> if p = pid then Some t else None) ins
                      |> Option.value ~default:0 in
          (try c_type_of_if1_ty env.tm (TM.find ty_id env.tm) with _ -> C.Basic "float")
        else if nid = 0 && dir = `In then
          let ty_id = ES.fold (fun ((_, _), (dn, dp), t) acc ->
            if dn = 0 && dp = pid && t <> 0 then Some t else acc
          ) gr.eset None |> Option.value ~default:0 in
          (try c_type_of_if1_ty env.tm (TM.find ty_id env.tm) with _ -> C.Basic "float")
        else C.Basic "float"
    | _ -> C.Basic "float"

let get_elem_type env gr nid =
  let ty_id = ES.fold (fun ((sn, sp), _, t) acc ->
    if sn = nid && sp = 0 && t <> 0 then Some t else acc
  ) gr.eset None |> Option.value ~default:0 in
  try
    match TM.find ty_id env.tm with
    | Array_dv et_id | Array_ty et_id -> TM.find et_id env.tm
    | _ -> Unknown_ty
  with _ -> Unknown_ty

let string_of_pragma = function
  | Name s | Ast_type s | Subscript s -> s
  | _ -> ""

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

let find_subgraph gr name =
  let target = String.uppercase_ascii name in
  let res = NM.choose_opt (NM.filter (fun _ n ->
    match n with
    | Compound (_, _, _, pr, _, _) ->
        List.exists (function
          | Name s | Ast_type s | Subscript s -> String.uppercase_ascii s = target
          | _ -> false) pr
    | _ -> false
  ) gr.nmap) in
  res
  |> Option.map (fun (_id, n) ->
      match n with
      | Compound (cid, _, _, _, g, _) -> (cid, g)
      | _ -> assert false)

(* Trace one hop backward from every boundary In-port (node 0 In, i.e. the
   subgraph's outputs).  If the source node is a SELECT, record it.

   Returns a list of (select_nid, boundary_port) pairs — one entry per output
   port of the subgraph that is fed by a SELECT node.

   In an IF subgraph the SELECT nodes are the phi/merge points: each one sits
   at the boundary, takes (predicate, then-result, else-result) as inputs, and
   its output is the subgraph result for that port.  Finding them here is the
   first step toward emitting a proper C if/else instead of a ternary. *)
let find_boundary_selects gr =
  ES.fold (fun ((sn, _sp), (dn, dp), _) acc ->
    if dn = 0 then
      match NM.find_opt sn gr.nmap with
      | Some (Simple (_, SELECT, _, _, _)) -> (sn, dp) :: acc
      | _ -> acc
    else acc
  ) gr.eset []

let topo_sort gr =
  let nodes = NM.bindings gr.nmap |> List.map fst in
  let num_nodes = List.length nodes in
  let in_degree = Hashtbl.create num_nodes in
  let adj_list = Hashtbl.create num_nodes in
  
  List.iter (fun id -> 
    Hashtbl.add in_degree id 0;
    Hashtbl.add adj_list id []
  ) nodes;

  (* Construct DAG using the edge-set.
     If edge starts at 0, it's from the boundary-input node (ignore for in-degree). *)
  ES.iter (fun ((sn, _), (dn, _), _) ->
    if sn <> 0 then begin
      if Hashtbl.mem in_degree dn && Hashtbl.mem adj_list sn then begin
        let current = Hashtbl.find in_degree dn in
        Hashtbl.replace in_degree dn (current + 1);
        let succs = Hashtbl.find adj_list sn in
        Hashtbl.replace adj_list sn (dn :: succs)
      end
    end
  ) gr.eset;

  let worklist = Queue.create () in
  List.iter (fun id ->
    if Hashtbl.find in_degree id = 0 then Queue.add id worklist
  ) nodes;

  let rec loop acc =
    if Queue.is_empty worklist then List.rev acc
    else
      let n = Queue.take worklist in
      let successors = Hashtbl.find adj_list n in
      List.iter (fun dn ->
        let d = Hashtbl.find in_degree dn - 1 in
        Hashtbl.replace in_degree dn d;
        if d = 0 then Queue.add dn worklist
      ) successors;
      loop (n :: acc)
  in
  let sorted = loop [] in
  if List.length sorted < num_nodes then begin
    (* Fallback for malformed graphs (e.g. unexpected cycles) *)
    let visited = Hashtbl.create num_nodes in
    List.iter (fun id -> Hashtbl.add visited id true) sorted;
    let missing = List.filter (fun id -> not (Hashtbl.mem visited id)) nodes in
    sorted @ missing
  end else
    sorted
