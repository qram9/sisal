(** Structural comparison of IF1 graphs.

    Two modes:

    1. {b Exact comparison}: walks both node maps and edge sets in lock-step,
       reporting every difference found (extra/missing nodes, opcode mismatches,
       literal value mismatches, type mismatches on edges).  Compound subgraphs
       are compared recursively.

    2. {b Tree/DAG match}: strips boundary edges (those incident to node 0),
       then represents each output as a [cdag_node] tree.  Two graphs are
       tree-equal when every corresponding output tree is equal.  Fan-out (value
       reuse) is handled by memoising already-visited (node, port) pairs so each
       shared sub-computation is only compared once. *)

open If1

(* --------------------------------------------------------------------------
   Helpers
   -------------------------------------------------------------------------- *)

(** Return the opcode string for a node, or a descriptive tag. *)
let node_label_str = function
  | Simple (_, sym, _, _, _)       -> Printf.sprintf "Simple(%s)" (string_of_node_sym sym)
  | Compound (_, sym, _, _, _, _)  -> Printf.sprintf "Compound(%s)" (string_of_node_sym sym)
  | Literal (_, code, v, _)        -> Printf.sprintf "Literal(%s:%s)" (string_of_if1_basic_ty code) v
  | Boundary _                     -> "Boundary"
  | Unknown_node                   -> "Unknown"

(** Edges incident to node 0 — the boundary. *)
let is_boundary_edge ((s, _), (d, _), _) = s = 0 || d = 0

(** All internal edges (neither endpoint is node 0). *)
let internal_edges gr =
  ES.filter (fun e -> not (is_boundary_edge e)) gr.eset

(* --------------------------------------------------------------------------
   1.  EXACT STRUCTURAL COMPARISON
   -------------------------------------------------------------------------- *)

(** A single detected difference between two graphs. *)
type diff =
  | Node_extra_left  of int * string          (** node in g1 missing from g2 *)
  | Node_extra_right of int * string          (** node in g2 missing from g1 *)
  | Node_opcode      of int * string * string (** id; g1 opcode; g2 opcode *)
  | Node_literal_val of int * string * string (** id; g1 value; g2 value *)
  | Node_literal_code of int * string * string (** id; g1 type; g2 type *)
  | Edge_extra_left  of (int*int) * (int*int) * int  (** (src,p),(dst,p),ty in g1 not g2 *)
  | Edge_extra_right of (int*int) * (int*int) * int  (** (src,p),(dst,p),ty in g2 not g1 *)
  | Edge_type        of (int*int) * (int*int) * int * int (** same endpoints, different types *)
  | Sub_mismatch     of int * diff list        (** compound node, inner diffs *)

(** Human-readable diff entry. *)
let rec string_of_diff = function
  | Node_extra_left  (id, tag)     -> Printf.sprintf "  +node %d (%s) only in left" id tag
  | Node_extra_right (id, tag)     -> Printf.sprintf "  +node %d (%s) only in right" id tag
  | Node_opcode      (id, a, b)    -> Printf.sprintf "  node %d opcode %s ≠ %s" id a b
  | Node_literal_val (id, a, b)    -> Printf.sprintf "  node %d literal value %s ≠ %s" id a b
  | Node_literal_code (id, a, b)   -> Printf.sprintf "  node %d literal type %s ≠ %s" id a b
  | Edge_extra_left  ((s,sp),(d,dp),t) ->
      Printf.sprintf "  +edge (%d:%d)→(%d:%d) ty=%d only in left" s sp d dp t
  | Edge_extra_right ((s,sp),(d,dp),t) ->
      Printf.sprintf "  +edge (%d:%d)→(%d:%d) ty=%d only in right" s sp d dp t
  | Edge_type ((s,sp),(d,dp),t1,t2) ->
      Printf.sprintf "  edge (%d:%d)→(%d:%d) type %d ≠ %d" s sp d dp t1 t2
  | Sub_mismatch (id, ds) ->
      Printf.sprintf "  compound node %d subgraph:\n%s"
        id (String.concat "\n" (List.map string_of_diff ds))

(** Result of a comparison. *)
type match_result =
  | Graphs_equal
  | Graphs_differ of diff list

let string_of_match_result = function
  | Graphs_equal      -> "Graphs_equal"
  | Graphs_differ ds  ->
      "Graphs_differ:\n" ^ String.concat "\n" (List.map string_of_diff ds)

(** Compare two individual nodes at the same ID.  Returns any diffs found. *)
let rec compare_one_node id n1 n2 : diff list =
  match n1, n2 with
  | Boundary _, Boundary _ -> []     (* boundary node contents are derived; skip *)
  | Unknown_node, Unknown_node -> []

  | Simple (_, sym1, pin1, pout1, _), Simple (_, sym2, pin2, pout2, _) ->
      let d1 = if sym1 = sym2 then []
               else [ Node_opcode (id,
                        string_of_node_sym sym1,
                        string_of_node_sym sym2) ]
      in
      let d2 = if Array.length pin1 = Array.length pin2 then []
               else [ Node_opcode (id,
                        Printf.sprintf "%s(in=%d)" (string_of_node_sym sym1) (Array.length pin1),
                        Printf.sprintf "%s(in=%d)" (string_of_node_sym sym2) (Array.length pin2)) ]
      in
      let d3 = if Array.length pout1 = Array.length pout2 then []
               else [ Node_opcode (id,
                        Printf.sprintf "%s(out=%d)" (string_of_node_sym sym1) (Array.length pout1),
                        Printf.sprintf "%s(out=%d)" (string_of_node_sym sym2) (Array.length pout2)) ]
      in
      d1 @ d2 @ d3

  | Literal (_, code1, v1, _), Literal (_, code2, v2, _) ->
      let d1 = if code1 = code2 then []
               else [ Node_literal_code (id,
                        string_of_if1_basic_ty code1,
                        string_of_if1_basic_ty code2) ]
      in
      let d2 = if String.equal v1 v2 then []
               else [ Node_literal_val (id, v1, v2) ]
      in
      d1 @ d2

  | Compound (_, sym1, lbl1, _, g1, _), Compound (_, sym2, lbl2, _, g2, _) ->
      let d1 = if sym1 = sym2 then []
               else [ Node_opcode (id,
                        string_of_node_sym sym1,
                        string_of_node_sym sym2) ]
      in
      let d2 = if lbl1 = lbl2 then []
               else [ Node_opcode (id,
                        Printf.sprintf "%s[label=%d]" (string_of_node_sym sym1) lbl1,
                        Printf.sprintf "%s[label=%d]" (string_of_node_sym sym2) lbl2) ]
      in
      let sub_diffs = compare_graphs_inner g1 g2 in
      let d3 = match sub_diffs with [] -> [] | ds -> [ Sub_mismatch (id, ds) ] in
      d1 @ d2 @ d3

  | _ ->
      (* Different constructors *)
      [ Node_opcode (id, node_label_str n1, node_label_str n2) ]

(** Compare edge sets, ignoring type ID differences (structural types matter). *)
and compare_edges_exact es1 es2 : diff list =
  (* Build a map  (src, srcp, dst, dstp) → type_id  for each set *)
  let to_key_map es =
    ES.fold (fun ((s,sp),(d,dp),t) acc ->
      let k = (s, sp, d, dp) in
      (* In case of duplicates (shouldn't happen in valid IF1), keep first *)
      if List.mem_assoc k acc then acc else (k, t) :: acc
    ) es []
  in
  let m1 = to_key_map es1 in
  let m2 = to_key_map es2 in
  (* Edges in es1 not in es2, or with different type *)
  let diffs_l =
    List.filter_map (fun ((s,sp,d,dp), t1) ->
      match List.assoc_opt (s,sp,d,dp) m2 with
      | None    -> Some (Edge_extra_left  ((s,sp),(d,dp), t1))
      | Some t2 -> if t1 = t2 then None
                   else Some (Edge_type ((s,sp),(d,dp), t1, t2))
    ) m1
  in
  (* Edges in es2 not in es1 *)
  let diffs_r =
    List.filter_map (fun ((s,sp,d,dp), t2) ->
      if List.mem_assoc (s,sp,d,dp) m1 then None
      else Some (Edge_extra_right ((s,sp),(d,dp), t2))
    ) m2
  in
  diffs_l @ diffs_r

(** Internal: collect diffs without wrapping in match_result. *)
and compare_graphs_inner g1 g2 : diff list =
  let nm1 = g1.nmap and nm2 = g2.nmap in

  (* Node diffs *)
  let node_diffs =
    (* Nodes in g1 *)
    let from_left =
      NM.fold (fun id n1 acc ->
        match NM.find_opt id nm2 with
        | None    -> Node_extra_left (id, node_label_str n1) :: acc
        | Some n2 -> compare_one_node id n1 n2 @ acc
      ) nm1 []
    in
    (* Extra nodes only in g2 *)
    let from_right =
      NM.fold (fun id n2 acc ->
        if NM.mem id nm1 then acc
        else Node_extra_right (id, node_label_str n2) :: acc
      ) nm2 []
    in
    from_left @ from_right
  in

  (* Edge diffs *)
  let edge_diffs = compare_edges_exact g1.eset g2.eset in

  node_diffs @ edge_diffs

(** Full structural comparison.  Compound subgraphs are compared recursively.
    Types on edges are compared by ID (assuming both graphs share the same
    typemap, as when one is derived from the other). *)
let compare_graphs g1 g2 : match_result =
  match compare_graphs_inner g1 g2 with
  | []   -> Graphs_equal
  | diffs -> Graphs_differ diffs

(* --------------------------------------------------------------------------
   2.  COMPUTATION DAG / TREE MATCH
   --------------------------------------------------------------------------

   Strip all edges incident to node 0.  Represent each output as a
   [cdag_node] tree.  Two graphs are "dag-equal" when every output tree
   matches.

   Fan-out (the same (node,port) feeding multiple consumers) is handled
   naturally: when tracing backwards we arrive at the same (node,port) from
   different paths and reconstruct the same [cdag_node]; since cdag_node is
   a value type and equality is structural, sharing is transparent.
   -------------------------------------------------------------------------- *)

(** A computation DAG node, produced by stripping boundary edges. *)
type cdag_node =
  | Cdag_input   of int
      (** Boundary input: the integer is the port on node 0.  Represents
          a function parameter or loop-carried variable. *)
  | Cdag_literal of basic_code * string
      (** A constant value. *)
  | Cdag_simple  of node_sym * cdag_node array
      (** A Simple node with opcode [sym] and one child per input port
          (indexed 0 … n-1, in port order).  Ports with no incoming edge
          get [Cdag_input (-1)] as a placeholder. *)
  | Cdag_compound of node_sym * int * cdag_node array * graph
      (** A Compound node: opcode, label, children feeding the sub-boundary,
          and the (raw) subgraph for deeper inspection. *)
  | Cdag_unknown  of int
      (** Node ID whose definition was not found — indicates a bug. *)

(** Equality on cdag_node trees (structural, no alpha-renaming of inputs). *)
let rec cdag_equal a b =
  match a, b with
  | Cdag_input p1,   Cdag_input p2   -> p1 = p2
  | Cdag_literal (c1,v1), Cdag_literal (c2,v2) -> c1 = c2 && String.equal v1 v2
  | Cdag_simple (s1,ch1), Cdag_simple (s2,ch2) ->
      s1 = s2
      && Array.length ch1 = Array.length ch2
      && Array.for_all2 cdag_equal ch1 ch2
  | Cdag_compound (s1,l1,ch1,_), Cdag_compound (s2,l2,ch2,_) ->
      s1 = s2 && l1 = l2
      && Array.length ch1 = Array.length ch2
      && Array.for_all2 cdag_equal ch1 ch2
  | Cdag_unknown i1, Cdag_unknown i2 -> i1 = i2
  | _ -> false

(** Build a [cdag_node] by tracing backwards from [(node_id, out_port)] in [gr].

    [memo] maps already-visited [(node_id, out_port)] to their tree, so shared
    sub-computations are not re-expanded (the tree references them by value).
    [seen] is the set of node IDs currently on the recursion stack — used to
    detect cycles (which should not exist in well-formed IF1 dataflow, but we
    guard against them anyway). *)
let build_cdag gr =
  (* Map: (src_node, src_port) → dst list.  Built from the internal (non-boundary) edges. *)
  let int_edges = internal_edges gr in

  (* For each node and input port, find which (src_node, src_port) feeds it. *)
  (* inv_map: (dst_node, dst_port) → (src_node, src_port) option *)
  let inv_map =
    ES.fold (fun ((sn,sp),(dn,dp),_) acc ->
      (* One producer per (dst_node, dst_port) in SSA-like dataflow *)
      let k = (dn, dp) in
      if List.mem_assoc k acc then acc   (* keep first; valid IF1 is single-producer *)
      else (k, (sn, sp)) :: acc
    ) int_edges []
  in

  let memo : ((int * int), cdag_node) Hashtbl.t = Hashtbl.create 32 in

  let rec trace ?(seen = []) node_id out_port =
    let key = (node_id, out_port) in
    match Hashtbl.find_opt memo key with
    | Some cached -> cached
    | None ->
        if List.mem node_id seen then
          Cdag_unknown node_id  (* cycle guard *)
        else begin
          let seen' = node_id :: seen in
          let result =
            match NM.find_opt node_id gr.nmap with
            | None -> Cdag_unknown node_id

            | Some (Boundary _) ->
                (* node 0 as source means we crossed a boundary-input edge.
                   out_port is the boundary input port number. *)
                Cdag_input out_port

            | Some (Literal (_, code, v, _)) ->
                Cdag_literal (code, v)

            | Some (Simple (_, sym, pin, _, _)) ->
                (* For each input port of this node, trace its producer *)
                let n_in = Array.length pin in
                let children = Array.init n_in (fun p ->
                  match List.assoc_opt (node_id, p) inv_map with
                  | None          -> Cdag_input (-1)   (* dangling — boundary or unconnected *)
                  | Some (sn, sp) ->
                      (* If the source is node 0, this is a boundary input *)
                      if sn = 0 then Cdag_input sp
                      else trace ~seen:seen' sn sp
                ) in
                Cdag_simple (sym, children)

            | Some (Compound (_, sym, lbl, _, sub, _)) ->
                (* The compound's inputs come from its sub-boundary outputs,
                   which are fed by the parent graph's edges into the compound.
                   We trace those parent-side producers. *)
                let sub_in_count =
                  match NM.find_opt 0 sub.nmap with
                  | Some (Boundary (_, out_ports, _, _)) -> List.length out_ports
                  | _ -> 0
                in
                let children = Array.init sub_in_count (fun p ->
                  (* port p on node 0 of sub-graph is fed from the parent graph
                     via an edge (sn,sp) → (compound_node_id, p) *)
                  match List.assoc_opt (node_id, p) inv_map with
                  | None          -> Cdag_input (-1)
                  | Some (sn, sp) ->
                      if sn = 0 then Cdag_input sp
                      else trace ~seen:seen' sn sp
                ) in
                Cdag_compound (sym, lbl, children, sub)

            | Some Unknown_node -> Cdag_unknown node_id
          in
          Hashtbl.add memo key result;
          result
        end
  in
  trace

(** Extract the list of output trees from a graph: one [cdag_node] per
    output port of the boundary node, in port order. *)
let graph_to_cdag gr : cdag_node list =
  let trace = build_cdag gr in
  match NM.find_opt 0 gr.nmap with
  | Some (Boundary (_, out_ports, _, _)) ->
      (* out_ports : (src_node, src_port) list — the actual result producers.
         They are stored in reverse order (head = most recently added). *)
      let ordered = List.rev out_ports in
      List.map (fun (sn, sp) ->
        if sn = 0 then Cdag_input sp   (* boundary pass-through *)
        else trace sn sp
      ) ordered
  | _ -> []

(** Are two graphs DAG-equal?  Compares output trees pairwise. *)
let dag_equal g1 g2 : bool =
  let t1 = graph_to_cdag g1 in
  let t2 = graph_to_cdag g2 in
  List.length t1 = List.length t2
  && List.for_all2 cdag_equal t1 t2

(** Structural comparison that uses the DAG representation.
    Gives a richer result than [dag_equal]. *)
let dag_compare g1 g2 : match_result =
  let t1 = graph_to_cdag g1 in
  let t2 = graph_to_cdag g2 in
  if List.length t1 <> List.length t2 then
    Graphs_differ
      [ Node_opcode (0,
          Printf.sprintf "outputs=%d" (List.length t1),
          Printf.sprintf "outputs=%d" (List.length t2)) ]
  else
    let diffs =
      List.mapi (fun i (a, b) ->
        if cdag_equal a b then None
        else Some (Node_opcode (-(i+1),
               Printf.sprintf "output[%d] tree mismatch (left)" i,
               Printf.sprintf "output[%d] tree mismatch (right)" i))
      ) (List.combine t1 t2)
      |> List.filter_map Fun.id
    in
    match diffs with [] -> Graphs_equal | ds -> Graphs_differ ds

(* --------------------------------------------------------------------------
   3.  PRETTY-PRINTING CDAG TREES
   -------------------------------------------------------------------------- *)

let rec string_of_cdag ?(indent = 0) node =
  let pad = String.make indent ' ' in
  match node with
  | Cdag_input p ->
      if p = -1 then pad ^ "?" else Printf.sprintf "%sIN[%d]" pad p
  | Cdag_literal (code, v) ->
      Printf.sprintf "%sLIT(%s:%s)" pad (string_of_if1_basic_ty code) v
  | Cdag_simple (sym, children) ->
      let header = Printf.sprintf "%s%s" pad (string_of_node_sym sym) in
      if Array.length children = 0 then header
      else
        let body =
          Array.to_list children
          |> List.mapi (fun i ch ->
               Printf.sprintf "%s  [%d]:\n%s"
                 pad i (string_of_cdag ~indent:(indent+4) ch))
          |> String.concat "\n"
        in
        header ^ "\n" ^ body
  | Cdag_compound (sym, lbl, children, _) ->
      let header = Printf.sprintf "%s%s[%d]" pad (string_of_node_sym sym) lbl in
      if Array.length children = 0 then header
      else
        let body =
          Array.to_list children
          |> List.mapi (fun i ch ->
               Printf.sprintf "%s  [%d]:\n%s"
                 pad i (string_of_cdag ~indent:(indent+4) ch))
          |> String.concat "\n"
        in
        header ^ "\n" ^ body
  | Cdag_unknown id ->
      Printf.sprintf "%sUNKNOWN(%d)" pad id

let string_of_cdag_list cdags =
  List.mapi (fun i t ->
    Printf.sprintf "output[%d]:\n%s" i (string_of_cdag ~indent:2 t)
  ) cdags
  |> String.concat "\n"
