(** apple_env.ml: Environment and GID management for the Apple Silicon lowering
    pass. This module provides the data structures needed to track port
    mappings, subgraph identities, and the global state during IF1 to C-AST
    translation. *)

open Ir.If1
module C = Ir.C_ast

type direction = [ `In | `Out ]
(** Port direction: `In for input ports, `Out for output ports. *)

(** FullPortMap: A mapping from a fully qualified port (GID, Node ID, Port ID,
    Direction) to a C expression. This is the primary mechanism for tracking
    dataflow bindings across different scopes. *)
module FullPortMap = Map.Make (struct
  type t = int * int * int * direction (* gid, node_id, port_id, direction *)

  let compare = compare
end)

(** PortSet: A set of fully qualified ports. *)
module PortSet = Set.Make (struct
  type t = int * int * int * direction

  let compare = compare
end)

(* ------------------------------------------------------------------ *)
(*  GID assignment: DFS traversal, sorted by node ID                  *)
(* ------------------------------------------------------------------ *)

(** GidMap: Maps a (parent_gid, compound_node_id) pair to a unique child GID.
    The GID (Graph ID) is used to distinguish between different instances of
    subgraphs (e.g., in nested loops). *)
module GidMap = Map.Make (struct
  type t = int * int (* parent_gid * compound_nid *)

  let compare = compare
end)

(** [compound_children_sorted gr] returns all compound children of a graph,
    sorted by their Node ID to ensure deterministic GID assignment. *)
let compound_children_sorted (gr : graph) =
  NM.bindings gr.nmap
  |> List.filter_map (fun (nid, node) ->
      match node with
      | Compound (_, _, _, _, sub_gr, _) -> Some (nid, sub_gr)
      | _ -> None)
  |> List.sort (fun (id1, _) (id2, _) -> compare id1 id2)

(** [build_gid_table root_gr] performs a DFS traversal of the compound node
    hierarchy to pre-assign unique GIDs to every subgraph. The root graph is
    assigned GID 0. *)
let build_gid_table (root_gr : graph) : int GidMap.t =
  let rec visit parent_gid gr (counter, map) =
    List.fold_left
      (fun (ctr, m) (nid, sub_gr) ->
        let gid = ctr in
        let m' = GidMap.add (parent_gid, nid) gid m in
        visit gid sub_gr (ctr + 1, m'))
      (counter, map)
      (compound_children_sorted gr)
  in
  snd (visit 0 root_gr (1, GidMap.empty))

(** [alloc_gid tbl parent_gid nid] retrieves the GID for a specific compound
    node's subgraph from the pre-built table, or falls back to a deterministic
    value derived from the inputs. *)
let alloc_gid (tbl : int GidMap.t) parent_gid nid =
  match GidMap.find_opt (parent_gid, nid) tbl with
  | Some gid -> gid
  | None -> 1_000_000 + (parent_gid * 1_000) + nid

(* ------------------------------------------------------------------ *)

module PortFanout = Map.Make (struct
  type t = int * int (* node_id * port_id *)
  let compare = compare
end)

module StringSet = Set.Make (String)

type env = {
  tm : if1_ty TM.t;
  var_map : C.expr FullPortMap.t;
  preds : (int * int * int * direction) FullPortMap.t;
  curr_gid : int;
  curr_gr : graph;
  parent_env : env option;
  force_gpu : bool;
  gid_table : int GidMap.t;
  fanout_map : int PortFanout.t;
  mandatory_ports : PortSet.t;
  seen_decls : StringSet.t;
}
(** [env]: The lowering environment.
    - [tm]: Type map for IF1 types.
    - [var_map]: Maps ports to C expressions (Id, Member, etc.).
    - [preds]: Maps ports to their dataflow predecessors.
    - [curr_gid]: GID of the graph currently being lowered.
    - [curr_gr]: The IF1 graph currently being lowered.
    - [parent_env]: The environment of the enclosing scope.
    - [force_gpu]: Flag to indicate if GPU kernels should be preferred.
    - [gid_table]: Pre-calculated table of GID assignments. *)
