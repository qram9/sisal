open Ir.If1
module C = Ir.C_ast

type direction = [ `In | `Out ]

module FullPortMap = Map.Make (struct
  type t = int * int * int * direction (* gid, node_id, port_id, direction *)

  let compare = compare
end)

module PortSet = Set.Make (struct
  type t = int * int * int * direction

  let compare = compare
end)

(* ------------------------------------------------------------------ *)
(*  GID assignment: DFS traversal, sorted by node ID                  *)
(* ------------------------------------------------------------------ *)

(* Maps (parent_gid, compound_node_id) -> child_gid.
   The root graph of a function is always gid 0.
   Children are assigned in DFS order, siblings sorted by node_id.
   Node IDs are the stable symbol-table integers — the right key for
   ordering.  Pragma names are NOT used here: they describe structural
   roles (BODY, GENERATOR, RESULTS …) and are only meaningful inside
   find_subgraph when locating subgraphs within FORALL/IF constructs. *)
module GidMap = Map.Make (struct
  type t = int * int (* parent_gid * compound_nid *)

  let compare = compare
end)

(* NM.bindings already returns nodes in ascending nid order (OCaml Map
   iterates keys in order), so the sort below is a no-op in practice.
   It is written explicitly to document the intended ordering contract. *)
let compound_children_sorted (gr : graph) =
  NM.bindings gr.nmap
  |> List.filter_map (fun (nid, node) ->
      match node with
      | Compound (_, _, _, _, sub_gr, _) -> Some (nid, sub_gr)
      | _ -> None)
  |> List.sort (fun (id1, _) (id2, _) -> compare id1 id2)

(* Pre-traversal: assign gids 1, 2, 3 … in DFS + ascending-nid order.
   The caller (lower_procedure) reserves 0 for the top-level function
   graph itself. *)
let build_gid_table (root_gr : graph) : int GidMap.t =
  let counter = ref 1 in
  let map = ref GidMap.empty in
  let rec visit parent_gid gr =
    List.iter
      (fun (nid, sub_gr) ->
        let gid = !counter in
        incr counter;
        map := GidMap.add (parent_gid, nid) gid !map;
        visit gid sub_gr)
      (compound_children_sorted gr)
  in
  visit 0 root_gr;
  !map

(* Fallback counter for subgraphs that were not in the pre-built table
   (e.g. dynamically discovered FORALL bodies via find_subgraph whose
   compound node was somehow missed). Large base avoids collisions. *)
let next_dyn_gid = ref 1_000_000

let alloc_gid (tbl : int GidMap.t) parent_gid nid =
  match GidMap.find_opt (parent_gid, nid) tbl with
  | Some gid -> gid
  | None ->
      let gid = !next_dyn_gid in
      next_dyn_gid := gid + 1;
      gid

(* ------------------------------------------------------------------ *)

type env = {
  tm : if1_ty TM.t;
  var_map : C.expr FullPortMap.t;
  preds : (int * int * int * direction) FullPortMap.t;
  curr_gid : int;
  curr_gr : graph;
  parent_env : env option;
  force_gpu : bool;
  gid_table : int GidMap.t;
}
