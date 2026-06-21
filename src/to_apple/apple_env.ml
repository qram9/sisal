(** apple_env.ml: Defines the environment and configuration for the Apple
    Silicon lowering pass. *)

module NM = Ir.If1.NM
module SM = Ir.If1.SM
module TM = Ir.If1.TM
module ES = Ir.If1.ES

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
module StringSet = Set.Make (String)

(** [Direction] distinguishes between input (parameters) and output (results). *)
type direction = [ `In | `Out ]

(** [PortSet] and [FullPortMap] allow for precise identification of graph ports. *)
module PortSet = Set.Make (struct
  type t = int * int * int * direction (* GID, NID, PID, Dir *)

  let compare = compare
end)

module FullPortMap = Map.Make (struct
  type t = int * int * int * direction

  let compare = compare
end)

module GidMap = Map.Make (struct
  type t = int * int

  let compare = compare
end)

module PortFanout = Map.Make (struct
  type t = int * int * int

  let compare = compare
end)

module C = Ir.C_ast

(** [env] maintains the state of the lowering pass across different graphs. *)
type env = {
  tm : Ir.If1.if1_ty TM.t;
  var_map : C.expr FullPortMap.t;
  type_table : C.c_type FullPortMap.t; (* Unified Type Table *)
  preds : C.expr FullPortMap.t;
  curr_gid : int;
  curr_gr : Ir.If1.graph;
  parent_env : env option;
  compound_nid_in_parent : int;
  seen_decls : StringSet.t;
  fanout_map : int PortFanout.t;
  mandatory_ports : PortSet.t;
  gid_table : int GidMap.t;
  parent_map : (int * int) IntMap.t;
  proc_map : string IntMap.t; (* Global node ID to procedure name *)
  proc_param_map : C.expr FullPortMap.t; (* Procedure GID, NID, PID, Dir -> param name *)
  gid_name_map : string IntMap.t; (* GID to human-readable scope name from compound pragma *)
  procedures_info : Ir.If1.graph IntMap.t; (* Fast lookup for procedure subgraphs *)
  force_gpu : bool;
}
