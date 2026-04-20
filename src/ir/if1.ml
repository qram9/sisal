(** GRAPH is best to build inside out, due to the language strictness that we
    need a node and ports tuple. AST visitor builds the GRAPH inside out.

    TESTS: we are able to look up nodes in IF1.NM with an integer

    TESTS: Edges are pairs of ints containing a pair of ints (node-id,port-id)
    for head of edge and one more pair for tail of edge. Finally all edges are
    typed, and we have an additional int for ty-id.

    Nodes are either | Simple of node-type (binary operators, for ex) (and a
    port array, that may hold an adjacency-list) | Compound nodes for subgraphs
    and graphs

    Node numbers must be unique only inside Graphs to allow for import/export.

    Graphs boundaries have some special properties. TODO: Description.

    Literal edges are 5 tuples: | Literal of dest node, port, ref to type label,
    string, comment

    TODO:

    Provide depth or breadth first visitors.

    Use adjacency lists on nodes for incoming/outgoing edges.

    Test type-id on edges.

    Add line number and file name for debug information.

    Label Scoping: TODO: Type must also be stored in the Top-level graph

    TODO: Need to see why we need create_subgraph_symtab *)

(* to get call stack for debug use
  let stack = Printexc.get_callstack 5 in
  (* Capture top 5 frames *)
  print_endline (Printexc.raw_backtrace_to_string stack);
  *)

open Ast
open Format
open Printf

let if1_msg lvl fmt = Debug.msg "if1" lvl fmt

(** TODO: FOLDING OF MULTIARITY SEEMS IFFY **)

module IntMap = Map.Make (struct
  type t = int

  let compare = compare
end)

module IntSet = Set.Make (struct
  type t = int

  let compare = compare
end)

module StringMap = Map.Make (struct
  type t = string

  let compare = compare
end)

type label_or_none = Som of int | Emp

type node_sym =
  | AADDH
  | AADDL
  | AADJUST
  | ABUILD
  | ACATENATE
  | ACREATE
  | ADD
  | AELEMENT
  | AFILL
  | AGATHER
  | AISEMPTY
  | ALIMH
  | ALIML
  | AND
  | AREMH
  | AREML
  | AREPLACE
  | ASCATTER
  | ASETL
  | ASIZE
  | BITAND
  | BITOR
  | BITXOR
  | BOUNDARY
  | CONSTANT
  | EQUAL
  | ERROR_NODE
  | FDIVIDE
  | FINALVALUE
  | GRAPH
  | GREATER
  | GREATER_EQUAL
  | IDIVIDE
  | INTERNAL
  | INVOCATION
  | LESSER
  | LESSER_EQUAL
  | MAT
  | MATBUILD
  | MATSPLAT
  | MATMUL
  | MATVECMUL
  | VECMATMUL
  | DOT
  | MULTIARITY
  | NEGATE
  | NOT
  | NOT_EQUAL
  | OLD
  | OR
  | RANGEGEN
  | RBUILD
  | REDUCE
  | REDUCELEFT
  | REDUCERIGHT
  | REDUCETREE
  | RELEMENTS
  | RREPLACE
  | SAPPEND
  | SBUILD
  | SELECT
  | STREAM
  | STRM_APPEND
  | STRM_EMPTY
  | STRM_FIRST
  | STRM_REST
  | SHL
  | SHR
  | ASHR
  | SUBTRACT
  | SWIZZLE
  | TAGCASE
  | TIMES
  | TYPECAST
  | VAL
  | VEC
  | VBUILD
  | VSPLAT
  | DV_CREATE
  | DV_ELEMENT
  | DV_REPLACE
  | DV_GATHER
  | DV_SCATTER
  | DV_RESHAPE
  | DV_SLICE       (* DV_SLICE(A, starts[], sizes[]) → zero-copy view *)
  | DV_PERMUTE     (* DV_PERMUTE(A, dims[]) → reorder strides, zero-copy *)
  | DV_ROTATE      (* DV_ROTATE(A, n) → circular shift *)
  | DV_COMPRESS    (* DV_COMPRESS(A, mask) → Array_sparse *)
  | DV_OUTERPRODUCT (* DV_OUTERPRODUCT(f, A, B) → outer product *)
  | DV_GRADE_UP    (* DV_GRADE_UP(A) → ascending sort indices, APL ⍋ *)
  | DV_GRADE_DOWN  (* DV_GRADE_DOWN(A) → descending sort indices, APL ⍒ *)
  | DV_SORT        (* DV_SORT(A) → sorted copy *)
  | DV_REVERSE     (* DV_REVERSE(A) → reversed view, APL monadic ⌽, zero-copy via stride *)
  | REDUCE_ALL     (* REDUCE_ALL(op, A) → scalar, no forall needed *)
  | MAP_NODE       (* MAP_NODE(f, A) → same-shape array, APL ¨, also EACH/APPLY *)
  | FOLDL_NODE     (* FOLDL_NODE(f, init, A) → scalar *)
  | FOLDR_NODE     (* FOLDR_NODE(f, init, A) → scalar *)
  | SCAN_NODE      (* SCAN_NODE(f, A) → prefix-scan array, same shape *)
  | BROADCAST_SCALAR (* BROADCAST_SCALAR(s, A) → replicate scalar to shape of A *)
  | ARGMAX_NODE      (* ARGMAX(A) or ARGMAX(A, axis) → index/indices of maximum *)
  | ARGMIN_NODE      (* ARGMIN(A) or ARGMIN(A, axis) → index/indices of minimum *)
  | NONZERO_NODE     (* NONZERO(A) → Array[int] indices where A ≠ 0 *)
  | WHERE_NODE       (* WHERE(cond, A, B) → element-wise select *)
  | REDUCE_AXIS      (* SUM/PRODUCT/LEAST/GREATEST(A, axis) → reduced array *)
  | MEAN_NODE        (* MEAN(A) or MEAN(A, axis) *)
  | VARIANCE_NODE    (* VARIANCE(A) or VARIANCE(A, axis) *)
  | STDDEV_NODE      (* STDDEV(A) or STDDEV(A, axis) *)
  | ANY_NODE         (* ANY(A) or ANY(A, axis) → boolean reduction *)
  | ALL_NODE         (* ALL(A) or ALL(A, axis) → boolean reduction *)
  | NORM_NODE        (* NORM(A, p) → p-norm scalar *)
  | CUMSUM_NODE      (* CUMSUM(A) → prefix sum, same shape *)
  | CUMPROD_NODE     (* CUMPROD(A) → prefix product, same shape *)
  | CONCAT_NODE      (* CONCAT(A, B) → concatenate along last axis *)
  | TILE_NODE        (* TILE(A, n) → repeat A n times *)
  | SQUEEZE_NODE     (* SQUEEZE(A) → drop all size-1 dimensions *)
  | EXPAND_NODE      (* EXPAND(A, k) → insert size-1 dimension at axis k *)
  | RAVEL_NODE       (* RAVEL(A) → rank-1 view, zero-copy if contiguous, APL monadic , *)
  | STENCIL_NODE     (* STENCIL(f, A, d0, d1, ..) → sliding window map *)
  | PAD_NODE         (* PAD(A, lo, hi [, fill]) → padded copy *)
  | INNERPRODUCT_NODE (* INNERPRODUCT(A,B): dot if rank-1, matmul if rank-2, feeds AMX *)
  | EINSUM_NODE      (* EINSUM("subscript", A, B, ...): general tensor contraction; subscript carried as Subscript pragma *)
  | GET_DOPE_VEC     (* GET_DOPE_VEC(A) → port 0: dope as array[{lo,stride,size}], port 1: A unchanged *)
  | SHAPE_CHECK      (* SHAPE_CHECK(A,B) → no normal output; error port fires SHAPE_MISMATCH if sizes differ *)
  | DV_CONFORM       (* DV_CONFORM(A,B) → port 0: common iteration shape, port 1: error flag (bool) *)
  | DV_NUM_RANK      (* DV_NUM_RANK(A) → integer rank *)
  | DV_DIMENSION     (* DV_DIMENSION(A, k) → triplet (base, stride, size) *)
  | DV_OFFSET_AT     (* DV_OFFSET_AT(A, i, common_shape) → byte offset for linear index i *)
  | DV_LOAD_LINEAR   (* DV_LOAD_LINEAR(A, offset) → element value *)
  | DV_RESHAPE_BY_SHAPE (* DV_RESHAPE_BY_SHAPE(A, shape_arr) → multi-rank Array_dv *)
  | CONV_H           (** Apple Silicon: Horizontal Convolution *)
  | CONV_V           (** Apple Silicon: Vertical Convolution *)
  | CONV_2D          (** Apple Silicon: 2D Convolution *)

type comment = C of string | CDollar of string

type basic_code =
  | BOOLEAN
  | BYTE
  | CHARACTER
  | DOUBLE
  | HALF
  | INTEGRAL
  | LONG
  | REAL
  | SHORT
  | UBYTE
  | UCHAR
  | UINT
  | ULONG
  | USHORT
  | BYTE2
  | BYTE3
  | BYTE4
  | BYTE8
  | BYTE16
  | CHAR2
  | CHAR3
  | CHAR4
  | CHAR8
  | CHAR16
  | DOUBLE2
  | DOUBLE3
  | DOUBLE4
  | DOUBLE8
  | DOUBLE16
  | FLOAT2
  | FLOAT3
  | FLOAT4
  | FLOAT8
  | FLOAT16
  | HALF2
  | HALF3
  | HALF4
  | HALF8
  | HALF16
  | INT2
  | INT3
  | INT4
  | INT8
  | INT16
  | LONG2
  | LONG3
  | LONG4
  | LONG8
  | LONG16
  | SHORT2
  | SHORT3
  | SHORT4
  | SHORT8
  | SHORT16
  | UBYTE2
  | UBYTE3
  | UBYTE4
  | UBYTE8
  | UBYTE16
  | UCHAR2
  | UCHAR3
  | UCHAR4
  | UCHAR8
  | UCHAR16
  | UINT2
  | UINT3
  | UINT4
  | UINT8
  | UINT16
  | ULONG2
  | ULONG3
  | ULONG4
  | ULONG8
  | ULONG16
  | USHORT2
  | USHORT3
  | USHORT4
  | USHORT8
  | USHORT16
  | MAT2
  | MAT3
  | MAT4
  | NULL
  | ARRAY
  | RECORD
  | STREAM
  | UNION

type label = int

type if1_ty =
  | Array_ty of label
  | Array_dv of label  (* elem type id; dope-vector array, rank implicit in the DV at runtime *)
  | Basic of basic_code
  | Function_ty of label * label * string
  | Multiple of basic_code
  | Record of label * label * string
  | Stream of label
  | Tuple_ty of label * label
  | Union of label * label * string
  | Unknown_ty
  | If1Type_name of label
  | Field of label list
  | Tag of label list
  | ERROR of string
  | Typed_error of label

type port = string

type pragma =
  | Bounds of int * int
  | SrcLine of int * int
  | OpNum of int
  | Ar of int
  | Of of int
  | Lazy
  | Name of string
  | Ref
  | Pointer
  | Contiguous
  | No_pragma
  | Ast_type of string
  | Subscript of string  (* carries einsum index string on EINSUM_NODE *)

exception Node_not_found of string
exception Val_is_found of int
exception List_is_found of int list
exception Sem_error of string

type ports = port array
type pragmas = pragma list

module N = struct
  type t = label

  let compare = Stdlib.compare
end

module T = struct
  type t = label

  let compare = Stdlib.compare
end

type port_idx = int

(**Edge module, to enable using Map and Set. Because no Fan-ins possible, each
   edge gets to be unique. *)
module E = struct
  type t = (N.t * port_idx) * (N.t * port_idx) * int

  let compare ((i, pi), (j, pj), t1) ((k, pk), (m, pm), t2) =
    let cv1 = compare i k in
    if cv1 = 0 then
      let cv2 = compare j m in
      if cv2 = 0 then
        let cv3 = compare pi pk in
        if cv3 = 0 then
          let cv4 = compare pj pm in
          if cv4 = 0 then compare t1 t2 else cv4
        else cv3
      else cv2
    else cv1
end

(* Look at an array of ints and locate elem in it.
   Throw an error, if elem is not found.*)
let rec find_port an_array curr_idx len elem =
  if Array.get an_array curr_idx = elem then curr_idx
  else if curr_idx + 1 = len then
    raise (Node_not_found "Fail to find elem in array")
  else find_port an_array (curr_idx + 1) len elem

let cate_nicer a b c =
  match b with "" -> a | _ -> ( match a with "" -> b | _ -> a ^ c ^ b)

let rec cate_list a c =
  match a with hd :: tl -> cate_nicer hd (cate_list tl c) c | [] -> ""

and cate_list_pad i a c =
  match a with
  | hd :: tl -> cate_nicer (String.make i ' ' ^ hd) (cate_list_pad i tl c) c
  | [] -> ""

module ES = Set.Make (E)
module NM = Map.Make (N)
module SM = Map.Make (String)
module MM = Map.Make (String)
module TM = Map.Make (T)
module AStrSet = Set.Make (String)

let type_trace : (int * string * string) list ref = ref []

let str_type_trace () =
  List.fold_left
    (fun acc (id, desc, stack) ->
      let entry =
        Printf.sprintf
          "--------------------------\nID: %d | Type: %s\nSource Trace:\n%s\n"
          id desc stack
      in
      acc ^ entry (* Concatenate current entry to the accumulator *))
    "=== SISAL TYPE HISTORY DUMP ===\n" (List.rev !type_trace)

(* Edge Trace: (Source Node * Port | Dest Node * Port | Type Description * Stack) *)
let edge_trace : (string * string * string * string) list ref = ref []
let node_trace : (string * string) list ref = ref []

let str_node_trace () =
  List.fold_left
    (fun acc (src, stack) ->
      let entry = src ^ stack in
      acc ^ entry)
    "=== SISAL NODE HISTORY DUMP ===\n" (List.rev !node_trace)

let str_edge_trace () =
  List.fold_left
    (fun acc (src, dest, ty_desc, stack) ->
      let entry =
        Printf.sprintf
          "--------------------------\n\
           EDGE: %s -> %s\n\
           TYPE: %s\n\
           Source Trace:\n\
           %s\n"
          src dest ty_desc stack
      in
      acc ^ entry)
    "=== SISAL EDGE HISTORY DUMP (Boundary Edges) ===\n" (List.rev !edge_trace)

let get_stack_trace n =
  let raw_stack = Printexc.get_callstack n in
  Printexc.raw_backtrace_to_string raw_stack

type graph = {
  nmap : node NM.t;
  eset : ES.t;
  symtab : if1_value SM.t * if1_value SM.t;
  typemap : int * if1_ty TM.t * int MM.t;
  w : int;
}
(** The graph datastructure used by If1: This record currently uses Map and
    Sets. I need to understand how this impacts performance to decide if other
    options like hashtab would be better. This record gets passed around
    heavily.

    The symbol table is a pair of maps, one for current level and one for parent
    level. It may be better to number the entries based on the hierarchy. It
    looks like other options like that may be better here. *)

and if1_value = {
  val_ty : int;
  val_name : string;
  val_def : int;
  def_port : int;
}
(** Symbol table entry. *)

and node =
  | Simple of N.t * node_sym * ports * ports * pragmas
  | Compound of N.t * node_sym * label * pragmas * graph * N.t list
  | Literal of N.t * basic_code * string * ports
  | Boundary of
      (label * int * string) list
      * (label * int) list
      * (label * int) list
      * pragmas
  | Unknown_node

(** Create an empty graph for a caller. Take an incoming typemap and use that
    for the typemap. Make sure that the typemap has essential types, BOOLEAN,
    REAL etc. First symtab is current symtab and second for parent. *)

let basic_types =
  [
    (1, Basic BOOLEAN);
    (2, Basic BYTE);
    (3, Basic CHARACTER);
    (4, Basic DOUBLE);
    (5, Basic HALF);
    (6, Basic INTEGRAL);
    (7, Basic LONG);
    (8, Basic REAL);
    (9, Basic SHORT);
    (10, Basic UBYTE);
    (11, Basic UCHAR);
    (12, Basic UINT);
    (13, Basic ULONG);
    (14, Basic USHORT);
    (15, Basic BYTE2);
    (16, Basic CHAR2);
    (17, Basic DOUBLE2);
    (18, Basic HALF2);
    (19, Basic INT2);
    (20, Basic LONG2);
    (21, Basic FLOAT2);
    (22, Basic SHORT2);
    (23, Basic UBYTE2);
    (24, Basic UCHAR2);
    (25, Basic UINT2);
    (26, Basic ULONG2);
    (27, Basic USHORT2);
    (28, Basic BYTE3);
    (29, Basic CHAR3);
    (30, Basic DOUBLE3);
    (31, Basic HALF3);
    (32, Basic INT3);
    (33, Basic LONG3);
    (34, Basic FLOAT3);
    (35, Basic SHORT3);
    (36, Basic UBYTE3);
    (37, Basic UCHAR3);
    (38, Basic UINT3);
    (39, Basic ULONG3);
    (40, Basic USHORT3);
    (41, Basic BYTE4);
    (42, Basic CHAR4);
    (43, Basic DOUBLE4);
    (44, Basic HALF4);
    (45, Basic INT4);
    (46, Basic LONG4);
    (47, Basic FLOAT4);
    (48, Basic SHORT4);
    (49, Basic UBYTE4);
    (50, Basic UCHAR4);
    (51, Basic UINT4);
    (52, Basic ULONG4);
    (53, Basic USHORT4);
    (54, Basic BYTE8);
    (55, Basic CHAR8);
    (56, Basic DOUBLE8);
    (57, Basic HALF8);
    (58, Basic INT8);
    (59, Basic LONG8);
    (60, Basic FLOAT8);
    (61, Basic SHORT8);
    (62, Basic UBYTE8);
    (63, Basic UCHAR8);
    (64, Basic UINT8);
    (65, Basic ULONG8);
    (66, Basic USHORT8);
    (67, Basic BYTE16);
    (68, Basic CHAR16);
    (69, Basic DOUBLE16);
    (70, Basic HALF16);
    (71, Basic INT16);
    (72, Basic LONG16);
    (73, Basic FLOAT16);
    (74, Basic SHORT16);
    (75, Basic UBYTE16);
    (76, Basic UCHAR16);
    (77, Basic UINT16);
    (78, Basic ULONG16);
    (79, Basic USHORT16);
    (80, Basic MAT2);
    (81, Basic MAT3);
    (82, Basic MAT4);
    (83, Basic NULL);
  ]

let basic_map_tyid inc_map =
  List.fold_left (fun mm (x, y) -> IntMap.add x y mm) inc_map basic_types

let rec get_empty_graph n m =
  (* 1. Initialize the base graph *)
  let nm = NM.add 0 (Boundary ([], [], [], [])) NM.empty in
  let initial_gr =
    {
      nmap = nm;
      eset = ES.empty;
      symtab = (SM.empty, SM.empty);
      typemap = (m, TM.empty, MM.empty);
      w = n;
    }
  in

  (* 2. Helper to add basic types (Integer, Real, etc.) to the typemap *)
  let add_basic_type_entry gr (id, t_def) =
    let _, td, tm = gr.typemap in
    {
      gr with
      typemap = (m, TM.add id t_def td, MM.add (rev_lookup_ty_name id) id tm);
    }
  in

  (* 3. Add basic types first so they exist for the function signatures *)
  let final_graph =
    List.fold_left add_basic_type_entry initial_gr basic_types
  in
  final_graph

(* 4. Generate the 'MOD' signatures for every numeric type in the basic list *)
(* basic_type_list should contain the type IDs
     like [Integer_ID; Real_ID; ...] *)

and get_node_label n =
  match n with
  | Simple (x, _, _, _, _) -> x
  | Compound (x, _, _, _, _, _) -> x
  | Literal (x, _, _, _) -> x
  | Boundary _ -> 0
  | Unknown_node ->
      raise (Sem_error "Internal compiler error: unreachable @get_node_label")

(** Lookup a record field by name. *)
and get_record_field in_gr anum field_namen =
  let tm = get_typemap_tm in_gr in
  let hasit = TM.mem anum tm in
  match hasit with
  | true -> (
      let rec_k = TM.find anum tm in
      match rec_k with
      | Record (ff, nft, namen) -> (
          match String.equal namen field_namen with
          | true -> (anum, ff)
          | false -> get_record_field in_gr nft field_namen)
      | _ -> (anum, anum))
  | false -> (anum, anum)

and get_graph_label in_gr = in_gr.w

and get_graph_from_label ii ingr =
  try
    match NM.find ii (get_node_map ingr) with
    | Compound (_, _, _, _, gg, _) -> gg
    | _ ->
        raise
          (Sem_error
             "Internal compiler error: expected compound node for label.")
  with _ -> failwith "get_graph_from_label"

and has_node i ingr = NM.mem i (get_node_map ingr)

and get_node_rank i ingr =
  let rec find_rank = function
    | Ar r :: _ -> r
    | _ :: tl -> find_rank tl
    | [] -> 1
  in
  match get_node i ingr with
  | Simple (_, _, _, _, p) -> find_rank p
  | Compound (_, _, _, p, _, _) -> find_rank p
  | _ -> 1

and get_node i ingr =
  try NM.find i (get_node_map ingr)
  with _ ->
    failwith
      ((let stack = Printexc.get_callstack 5 in
        Printexc.raw_backtrace_to_string stack)
      ^ " ISSUE WITH NODE LOOK UP")

and get_symtab in_gr = in_gr.symtab
and get_typemap in_gr = in_gr.typemap
and get_node_map in_gr = in_gr.nmap
and get_edge_set in_gr = in_gr.eset
and get_node_map_and_edge_set in_gr = (in_gr.nmap, in_gr.eset)
and get_graph_in_compound_node (_, _, _, _, g, _) = g

and get_symtab_for_new_scope in_gr =
  let cs, ps = get_symtab in_gr in
  { in_gr with symtab = (SM.empty, SM.fold (fun k v z -> SM.add k v z) cs ps) }

(** Union other_ps, ps and other_cs. Then make it the new parent symtab with cs
    unchanged. *)
and inherit_parent_syms other_gr in_gr =
  let other_cs, other_ps = get_symtab other_gr in
  let cs, ps = get_symtab in_gr in
  {
    in_gr with
    symtab =
      ( cs,
        let kkk = fun k v z -> SM.add k v z in
        SM.fold kkk other_cs (SM.fold kkk other_ps ps) );
  }

(** Weird case, where we copy local syms to other only if they are not parent
    syms in other. *)
and create_subgraph_symtab in_gr other_gr =
  let cs = get_local_symtab in_gr in
  let otm = get_typemap in_gr in
  let other_cs, other_ps = get_symtab other_gr in
  let new_cs, other_gr =
    SM.fold
      (fun k entry (acc_cs, acc_gr) ->
        if SM.mem k other_ps = false then
          let port, acc_gr =
            add_to_boundary_inputs ~namen:entry.val_name entry.val_def
              entry.def_port acc_gr
          in
          ( SM.add k { entry with val_def = 0; def_port = port } acc_cs,
            acc_gr )
        else (acc_cs, acc_gr))
      cs (other_cs, other_gr)
  in
  let { nmap = nm; eset = es; symtab = _; typemap = tm; w = i } = other_gr in
  {
    nmap = nm;
    eset = es;
    symtab = (new_cs, other_ps);
    typemap = merge_typeblobs tm otm;
    w = i;
  }

and get_boundary_node in_gr =
  let nm = get_node_map in_gr in
  NM.find 0 nm

and string_of_list_of_list alist_lis out_s =
  match alist_lis with
  | ahd :: atl ->
      string_of_list_of_list atl
        ("["
        ^ String.concat ";" (List.map (fun (_, y) -> string_of_int y) ahd)
        ^ "]")
  | _ -> out_s

and string_of_height_list height_list height_num =
  match height_list with
  | alis_lis :: alis_tl ->
      cate_nicer
        (string_of_int height_num ^ " : " ^ string_of_list_of_list alis_lis "")
        (string_of_height_list alis_tl (height_num + 1))
        "\n"
  | [] -> ""

and string_of_5_ints (a, b, c, d, e) =
  (* Print a single predecessor, represented
       as a 5 tup *)
  "["
  ^ String.concat ";"
      (string_of_node_sym (num_to_node_sym a)
      :: List.map string_of_int [ b; c; d; e ])
  ^ "]"

and string_of_pred_lis anod map_pred =
  (* Given a node number, print its predecessors *)
  if IntMap.mem anod map_pred = true then
    List.fold_left
      (fun zz cur -> cate_nicer zz (string_of_5_ints cur) ";")
      ""
      (IntMap.find anod map_pred)
  else ""

and get_pred_lis anod map_pred =
  if IntMap.mem anod map_pred = true then
    List.fold_right
      (fun cur zz ->
        let a, b, c, d, e = cur in
        a :: b :: c :: d :: e :: zz)
      (IntMap.find anod map_pred)
      [ -1 ]
  else [ anod; -1 ]

and sort_maps amap =
  (* Sort incoming edges by incoming port#, field#4*)
  let compare_5 (_, _, _, a, _) (_, _, _, b, _) = compare a b in
  IntMap.fold
    (fun ke va ret_map -> IntMap.add ke (List.sort compare_5 va) ret_map)
    amap IntMap.empty

and fold_pred_to_one_lis anod map_pred =
  if IntMap.mem anod map_pred = true then
    let pred_lis = IntMap.find anod map_pred in
    let pred_lis =
      List.fold_right
        (fun (a, b, c, d, e) zz -> a :: b :: c :: d :: e :: -1 :: zz)
        pred_lis []
    in
    pred_lis @ [ -1; anod ]
  else []

and append_or_add rev_h nod num =
  if IntMap.mem num rev_h = true then
    IntMap.add num (IntSet.add nod (IntMap.find num rev_h)) rev_h
  else IntMap.add num (IntSet.add nod IntSet.empty) rev_h

and max_of_preds cur_max alis h rev_h map_pred cur_gr =
  match alis with
  | [] -> (cur_max, h, rev_h)
  | (_, ahd, _, _, _) :: atl ->
      let h, rev_h = get_height ahd map_pred h rev_h cur_gr in
      let ahd_h = IntMap.find ahd h in
      let cur_max, h, rev_h =
        if cur_max < ahd_h then (ahd_h, h, rev_h) else (cur_max, h, rev_h)
      in
      max_of_preds cur_max atl h rev_h map_pred cur_gr

and get_height cur map_pred h rev_h cur_gr =
  if cur = 0 then (IntMap.add cur 0 h, append_or_add rev_h cur 0)
  else if IntMap.mem cur h = true then (h, rev_h)
  else
    let cur_h, h, rev_h =
      if IntMap.mem cur map_pred = false then (0, h, rev_h)
      else
        let ret_h, h, rev_h =
          (max_of_preds 0 (IntMap.find cur map_pred) h rev_h) map_pred cur_gr
        in
        (ret_h + 1, h, rev_h)
    in
    (IntMap.add cur cur_h h, append_or_add rev_h cur cur_h)

and initialize_exp_info es nm =
  ES.fold
    (fun ((x, xp), (y, yp), ed_ty) (node_l, nm, init_height, map_succ, map_pred)
       ->
      let node_l, init_height =
        match IntMap.mem x init_height with
        | true -> (node_l, init_height)
        | false -> (x :: node_l, IntMap.add x 0 init_height)
      in
      let xnm = NM.find x nm in
      let ynm = NM.find y nm in
      let xn =
        match xnm with
        | Simple (_, n, _, _, _) -> n
        | Boundary _ -> BOUNDARY
        | Unknown_node ->
            raise (Sem_error "Internal, unreachable cse_height_xn")
        | Literal _ -> CONSTANT
        | Compound (_, _, _, _, _, _) -> GRAPH
      in

      let yn =
        match ynm with
        | Simple (_, n, _, _, _) -> n
        | Boundary _ -> BOUNDARY
        | Literal _ -> CONSTANT
        | Unknown_node ->
            raise (Sem_error "Internal, unreachable cse_height_yn")
        | Compound (_, _, _, _, _, _) -> GRAPH
      in

      if xn <> GRAPH && yn <> GRAPH then
        (* True body when xn and yn are not GRAPHS *)
        let map_succ =
          match IntMap.mem x map_succ with
          | true ->
              IntMap.add x
                ((node_sym_to_num xn, xp, y, yp, ed_ty)
                :: IntMap.find x map_succ)
                map_succ
          | false ->
              IntMap.add x
                ((node_sym_to_num xn, xp, y, yp, ed_ty) :: [])
                map_succ
        in
        let map_pred =
          match IntMap.mem y map_pred with
          | true ->
              IntMap.add y
                ((node_sym_to_num yn, x, xp, yp, ed_ty)
                :: IntMap.find y map_pred)
                map_pred
          | false ->
              IntMap.add y
                ((node_sym_to_num yn, x, xp, yp, ed_ty) :: [])
                map_pred
        in
        let map_pred = sort_maps map_pred in
        let map_succ = sort_maps map_succ in
        (node_l, nm, init_height, map_succ, map_pred)
      else
        (* False Body when either xn and yn are GRAPHS.
           Not sure what to do here.*)
        (node_l, nm, init_height, map_succ, map_pred))
    (* ES.fold input *) es
    (* ES.fold output *) ([], nm, IntMap.empty, IntMap.empty, IntMap.empty)

and visit_block ablk mymap (directory, capF) =
  match ablk with
  | (cur_pos, ahd) :: atl ->
      let blk_content = IntMap.find ahd mymap in
      let nth = List.nth blk_content cur_pos in
      let directory =
        if IntMap.mem nth directory = false then
          IntMap.add nth [ (cur_pos, ahd) ] directory
        else
          IntMap.add nth ((cur_pos, ahd) :: IntMap.find nth directory) directory
      in
      let capF =
        if IntSet.mem ahd capF = false then IntSet.add ahd capF else capF
      in
      visit_block atl mymap (directory, capF)
  | [] -> (directory, capF)

and inc_pos alis = List.fold_right (fun (x, y) ou -> (x + 1, y) :: ou) alis []

and print_a_finished_one sentinel alis mymap =
  let string_of_int_pair (x, y) =
    "("
    ^ string_of_int (x + 1)
    ^ "," ^ string_of_int y ^ " aka ["
    ^ String.concat "; " (List.map string_of_int (IntMap.find y mymap))
    ^ "])"
  in
  sentinel ^ String.concat ";" (List.map string_of_int_pair alis) ^ "\n"

(** Each entry in alis is value-numbered to the witness named cur. *)
and get_vn_table alis cur outm =
  match alis with
  | (_, hd) :: tl -> get_vn_table tl cur (IntMap.add hd cur outm)
  | [] -> outm

and update_a_list ahd vns =
  List.map
    (fun x -> if IntMap.mem x vns = true then IntMap.find x vns else x)
    ahd

and update_vns ablk vns new_mymap =
  match ablk with
  | (_, ahd) :: atl ->
      let updated_map =
        (* output map *)
        IntMap.add ahd (* key *)
          (update_a_list (IntMap.find ahd new_mymap) vns) (* value *)
          new_mymap
        (* input map *)
      in
      update_vns atl vns updated_map
  | [] -> new_mymap

(** This is the inner function that calls visit_block for each blocks in the
    blks list to see if they are finished. *)
and visit_block_list blks vns mymap =
  match blks with
  | ahd :: atl ->
      let ff, _ =
        visit_block ahd (update_vns ahd vns mymap) (IntMap.empty, IntSet.empty)
      in
      (* Figure out the cases that finished
       and cases that are still being updated. *)
      let not_yet_done, done_ones =
        IntMap.fold
          (fun ke valu (not_done, all_done) ->
            if ke = -1 then (
              ( not_done,
                let _, s = List.hd valu in
                print_string
                  ("(REACHED SENTINEL) WITNESS:" ^ string_of_int s ^ " FOR "
                  ^ string_of_int (List.length valu)
                  ^ " TREES"
                  ^ print_a_finished_one " :- " valu mymap);
                get_vn_table valu s all_done ))
            else if List.length valu = 1 then
              ( not_done,
                (print_string (print_a_finished_one "SIZE 1 :- " valu mymap);
                 let _, s = List.hd valu in
                 print_endline ("WITNESS:" ^ string_of_int s);
                 get_vn_table valu s all_done) )
            else (inc_pos valu :: not_done, all_done))
          ff ([], vns)
      in
      let to_follow = atl @ not_yet_done in
      visit_block_list to_follow done_ones mymap
  | [] -> vns

(** We have a block list at each height. This function traverses by height (0,N)
    and calls visit_block at each. *)
and visit_by_height mymap height_list vns height_num =
  match height_list with
  | alis :: tl ->
      print_endline "-------------------";
      print_endline ("At Height:" ^ string_of_int height_num);
      let vns = visit_block_list alis vns mymap in
      visit_by_height mymap tl vns (height_num + 1)
  | [] -> vns

(** Each edge starts at a node,port and ends at another node,port. (x,xp) ->
    (y,yp), with type ed_ty: (x,xp,y,yp,ed_ty). Pred of y, is a reversing of the
    arrow or by adjusting the tuple like this: (yp,x,xp,ed_ty): incoming port is
    yp, src# is x, src out-port is xp, type ed_ty. Similarly, for each x, the
    tuples that describe the arrow going out is (xp,y,yp,ed_ty). That shall be
    used along with the opcode, xn, to describe the outgoing edge. Similarly,
    (yn,y,yp,xp,ed_ty) will describe a succ-edge with the node-type of y: yn.
    Suppose we have a binary operation, for ex, opcode:ADD, Preds:
    Op1:(xp1,y1,yp1,ed_ty) Op2:(xp2,y2,yp2,ed_ty). Folding the tree to a list
    gives: [ADD;xp1;y1;yp1;ed_ty;xp2;y2;yp2;ed_ty] A duplicate operation needs
    to have the same content as above. TODO: How do we do this for calls?!? Must
    we have a compare function that accepts a node-sym variant? 1:A height
    relation is first obtained. The height relation function is called
    get_height. It would start with the height of incoming boundary node to 0.
    Then the height of internal nodes are calculated by getting the max of
    children heights, with a recursive walk that ends on the outgoing boundary
    node, again numbered 0. 2:The cse algorithm operates from inner-most graphs
    outwards, in post-order. The top-level is called cse_by_part. For each
    graph, CSE goes up the height relation and DAGifys, that is, it provides
    value numbers to each of the unique trees at a current height. Height is
    incremented, but before processing the nodes at the incremented height, the
    vn table must be checked and current lists updated.*)
and cse_by_part in_gr = in_gr
(*
  let { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } = in_gr in
  let nm =
    NM.fold
      (fun _ nod last_nm ->
        let last_nm =
          match nod with
          | Simple (_, _, _, _, _) -> last_nm
          | Boundary _ -> last_nm
          | Unknown_node ->
              raise (Sem_error "Internal, unreachable cse_height_xn")
          | Literal _ -> last_nm
          | Compound (lab, sy, ty, pl, subgr, assoc) ->
              let subgr = cse_by_part subgr in
              NM.add lab (Compound (lab, sy, ty, pl, subgr, assoc)) last_nm
        in
        last_nm)
      nm nm
  in
  let node_l, nm, _, _, map_pred = initialize_exp_info es nm in
  let cur_gr = { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } in
  (*print_endline
    ("PRED_MAP:\n" ^
       (IntMap.fold (
            fun nod ed z ->
            (string_of_int nod) ^
              (" -> " ^
                 (List.fold_right
                    (fun x y ->
                      cate_nicer
                        (string_of_5_ints x) y ",")
                    ed ""))) map_pred ""));
    print_endline
    ("SUCC_MAP:\n" ^
       (IntMap.fold (
            fun nod ed z ->
            (string_of_int nod) ^
              (" -> " ^
                 (List.fold_right
                    (fun x y ->
                      cate_nicer
                        (string_of_5_ints x) y ",")
                    ed ""))) map_succ ""));*)
  let _, rev_height_map =
    List.fold_left
      (fun (height_map, rev_h) cur ->
        get_height cur map_pred height_map rev_h cur_gr)
      (IntMap.empty, IntMap.empty)
      node_l
  in
  (*print_endline
    ("Height:\n" ^
       (IntMap.fold (
            fun nod h z ->
            (string_of_int nod) ^
              " -> " ^ (string_of_int h) ^ "\n" ^ z)
          height_map ""));*)
  let nodes_by_height = IntMap.bindings rev_height_map in
  let my_lis_lis =
    List.fold_right
      (fun (_, set) last_lis ->
        [ List.map (fun x -> (0, x)) (IntSet.elements set) ] :: last_lis)
      nodes_by_height []
  in
  let mymap =
    IntMap.fold
      (fun _ h last_m ->
        IntSet.fold
          (fun cur last_map ->
            IntMap.add cur (get_pred_lis cur map_pred) last_map)
          h last_m)
      rev_height_map IntMap.empty
  in
  (* print_endline "CONTENT MAP";
     (IntMap.fold (fun x y z ->
       print_int x; print_char ':';
       print_endline (
           String.concat ";"
             (List.map string_of_int y));
       "") mymap "");
     print_endline
     ("RevHeight:\n" ^
       (IntMap.fold (
            fun nod h z ->
            (string_of_int nod) ^
              " -> " ^
                (IntSet.fold
                   (fun cur yy ->
                     (cate_nicer
                        (cate_nicer
                           (string_of_int cur)
                           (string_of_pred_lis cur map_pred) ":")
                        yy "\n     "))
                   h "") ^ "\n" ^ z)
          rev_height_map ""));*)
  let _ =
    IntMap.fold
      (fun nod ed z ->
        IntMap.add nod
          (IntSet.fold
             (fun cur yy ->
               let folded_lis = fold_pred_to_one_lis cur map_pred in
               folded_lis :: yy)
             ed [])
          z)
      rev_height_map IntMap.empty
  in
  (* let height_bound_blocks =
     IntMap.bindings rev_height_map_folded in
     print_endline
     (List.fold_right
       (fun (xh,blocks) last_set ->
         cate_nicer
           ("AT HEIGHT:" ^ (string_of_int xh) ^ "\n" ^
              (List.fold_right
                 (fun blk last_blk ->
                   cate_nicer
                     ("    {" ^
                        (String.concat ";"
                           (List.map string_of_int blk)) ^ "}")
                     last_blk
                     "\n")
                 blocks ""))
           last_set
           "\n") height_bound_blocks "");*)
  let vns = visit_by_height mymap my_lis_lis IntMap.empty 1 in
  print_endline "Val-nums";
  print_string
    (IntMap.fold
       (fun x y las ->
         let x, y = (string_of_int x, string_of_int y) in
         String.concat "\n" [ String.concat " -> " [ x; y ]; las ])
       vns "");
  let es =
    ES.fold
      (fun ((x, xp), (y, yp), y_ty) res ->
        let x = if IntMap.mem x vns = true then IntMap.find x vns else x in
        ES.add ((x, xp), (y, yp), y_ty) res)
      es ES.empty
  in
  let res_gr = { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } in
  let _ = dot_graph res_gr in
  res_gr
  *)

and add_to_boundary_outputs ?(start_port = 0) srcn srcp tty in_gr =
  match get_boundary_node in_gr with
  | Boundary (in_port_list, out_port_list, err_ports, boundary_p) ->
      let { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } = in_gr in
      let annod =
        match NM.find_opt srcn nm with
        | Some x -> x
        | None ->
            failwith
              ("exception in add_to_boundary_outputs" ^ string_of_int srcn)
      in
      let start_port =
        if start_port = 0 then List.length out_port_list else start_port
      in
      add_edge2 srcn srcp 0 start_port tty
        {
          nmap =
            NM.add 0
              (Boundary
                 ( in_port_list,
                   (srcn, srcp) :: out_port_list,
                   err_ports,
                   boundary_p ))
              (NM.add srcn annod nm);
          eset = es;
          symtab = sm;
          typemap = tm;
          w = pi;
        }
  | _ -> in_gr

and get_named_input_ports in_gr =
  match get_boundary_node in_gr with
  | Boundary (in_port_list, _, _, _) -> in_port_list
  | _ -> []

and get_named_input_port_map in_gr =
  match get_boundary_node in_gr with
  | Boundary (in_port_list, _, _, _) ->
      List.fold_right
        (fun (_, yy, zz) output_map -> StringMap.add zz yy output_map)
        in_port_list StringMap.empty
  | _ -> StringMap.empty

and add_to_boundary_inputs ?(namen = "") n p in_gr =
  match get_boundary_node in_gr with
  | Boundary (in_port_list, out_port_list, err_ports, boundary_p) ->
      let rec lookin_lis idx = function
        | [] -> None
        | (x, y, _) :: _ when n = x && p = y -> Some idx
        | _ :: tl -> lookin_lis (idx + 1) tl
      in
      let existing_idx_opt = lookin_lis 0 (List.rev in_port_list) in
      (match existing_idx_opt with
      | Some idx -> (idx, in_gr)
      | None ->
          let next_port = List.length in_port_list in
          let nm = get_node_map in_gr in
          ( next_port,
            {
              in_gr with
              nmap =
                NM.add 0
                  (Boundary
                     ( (n, p, namen) :: in_port_list,
                       out_port_list,
                       err_ports,
                       boundary_p ))
                  nm;
            } ))
  | _ -> (0, in_gr)

and boundary_in_port_count in_gr =
  match get_boundary_node in_gr with
  | Boundary (in_port_list, _, _, _) -> List.length in_port_list
  | _ -> 0

and boundary_out_port_count in_gr =
  match get_boundary_node in_gr with
  | Boundary (_, out_port_list, _, _) -> List.length out_port_list
  | _ -> 0

and get_old_var_port vv in_gr =
  let cs = fst (get_symtab in_gr) in
  let old_name = "OLD " ^ vv in
  if SM.mem old_name cs = true then
    let { val_name = _; val_ty = _; val_def = _; def_port = cou } =
      SM.find old_name cs
    in
    `Found_one cou
  else `Not_there

and defs_of_bound_names in_gr =
  let cs = fst (get_symtab in_gr) in
  SM.fold
    (fun k { val_name = _; val_ty = _; val_def = def; def_port = _ } xx ->
      IntMap.add def k xx)
    cs IntMap.empty

and dump_boundary_outputs in_gr =
  let tm = get_typemap_tm in_gr in
  let edges =
    ES.fold
      (fun ((srcn, srcp), (dstn, dstp), ty) acc ->
        if dstn = 0 then (srcn, srcp, dstp, ty) :: acc else acc)
      in_gr.eset []
    |> List.sort (fun (_, _, p1, _) (_, _, p2, _) -> compare p1 p2)
  in
  if1_msg 3 "boundary: %d output port(s)" (List.length edges);
  List.iter
    (fun (srcn, srcp, dstp, ty) ->
      if1_msg 3 "  edge %d:%d -> 0:%d [%s]" srcn srcp dstp
        (printable_full_type tm ty))
    edges

and output_bound_names_for_subgraphs ?(_start_port = 0) alis in_gr =
  let alis = List.rev alis in
  let bound_ports = defs_of_bound_names in_gr in
  if1_msg 3 "output_bound_names: %d candidate(s), %d bound name(s) in symtab"
    (List.length alis)
    (IntMap.cardinal bound_ports);
  let out_gr =
    List.fold_left
      (fun (idx, in_gr_) (x, y, z) ->
        if IntMap.mem x bound_ports then (
          let vname = IntMap.find x bound_ports in
          match get_old_var_port vname in_gr with
          | `Not_there ->
              if1_msg 4
                "output_bound_names: port %d node=%d (%s) bound but no OLD \
                 var, wiring to boundary"
                idx x vname;
              (idx + 1, add_to_boundary_outputs ~start_port:idx x y z in_gr_)
          | `Found_one _cou ->
              if1_msg 4
                "output_bound_names: port %d node=%d (%s) OLD var, wiring to \
                 boundary"
                idx x vname;
              (idx + 1, add_edge2 x y 0 idx z in_gr_))
        else begin
          if1_msg 4
            "output_bound_names: port %d node=%d not bound, wiring to boundary"
            idx x;
          (idx + 1, add_to_boundary_outputs ~start_port:idx x y z in_gr_)
        end)
      (0, in_gr) alis
    |> snd
  in
  dump_boundary_outputs out_gr;
  out_gr

and output_to_boundary ?(start_port = 0) alis in_gr =
  match alis with
  | (srcn, srcp, tyy) :: tl ->
      let srcn, srcp, tyy =
        find_incoming_regular_node (srcn, srcp, tyy) in_gr
      in
      output_to_boundary tl
        (add_to_boundary_outputs ~start_port srcn srcp tyy in_gr)
  | [] -> in_gr

and output_to_boundary_with_none ?(start_port = 0) alis in_gr =
  match alis with
  | Some (srcn, srcp, tyy) :: tl ->
      let srcn, srcp, tyy =
        find_incoming_regular_node (srcn, srcp, tyy) in_gr
      in
      output_to_boundary_with_none tl
        (add_to_boundary_outputs ~start_port srcn srcp tyy in_gr)
  | None :: tl -> output_to_boundary_with_none tl in_gr
  | [] -> in_gr

and input_from_boundary alis in_gr =
  match alis with
  | (srcn, srcp, nam) :: tl ->
      let _, in_gr = add_to_boundary_inputs ~namen:nam srcn srcp in_gr in
      input_from_boundary tl in_gr
  | [] -> in_gr

and get_element_type vect =
  match vect with
  | Basic vv -> Basic (get_element_type_impl vv)
  | _ ->
      print_endline (Printexc.get_backtrace ());
      failwith
        (Printf.sprintf "Cannot get element type for %s, only for vector types"
           (string_of_if1_ty vect))

and get_element_type_code vect =
  match vect with
  | Basic vv -> get_element_type_impl vv
  | _ ->
      print_endline (Printexc.get_backtrace ());
      failwith
        (Printf.sprintf "Cannot get element type for %s, only for vector types"
           (string_of_if1_ty vect))

(* Helper to extract the scalar "flavor" and the width *)
and get_element_type_impl vect =
  match vect with
  | BYTE2 | BYTE3 | BYTE4 | BYTE8 | BYTE16 -> BYTE
  | CHAR2 | CHAR3 | CHAR4 | CHAR8 | CHAR16 -> CHARACTER
  | HALF2 | HALF3 | HALF4 | HALF8 | HALF16 -> HALF
  | SHORT2 | SHORT3 | SHORT4 | SHORT8 | SHORT16 -> SHORT
  | INT2 | INT3 | INT4 | INT8 | INT16 -> INTEGRAL
  | LONG2 | LONG3 | LONG4 | LONG8 | LONG16 -> LONG
  | FLOAT2 | FLOAT3 | FLOAT4 | FLOAT8 | FLOAT16 -> REAL
  | DOUBLE2 | DOUBLE3 | DOUBLE4 | DOUBLE8 | DOUBLE16 -> DOUBLE
  | UBYTE2 | UBYTE3 | UBYTE4 | UBYTE8 | UBYTE16 -> UBYTE
  | UCHAR2 | UCHAR3 | UCHAR4 | UCHAR8 | UCHAR16 -> UCHAR
  | USHORT2 | USHORT3 | USHORT4 | USHORT8 | USHORT16 -> USHORT
  | UINT2 | UINT3 | UINT4 | UINT8 | UINT16 -> UINT
  | ULONG2 | ULONG3 | ULONG4 | ULONG8 | ULONG16 -> ULONG
  | HALF -> HALF
  | DOUBLE -> DOUBLE
  | REAL -> REAL
  | UINT -> UINT
  | UCHAR -> UCHAR
  | CHARACTER -> CHARACTER
  | BYTE -> BYTE
  | UBYTE -> UBYTE
  | INTEGRAL -> INTEGRAL
  | SHORT -> SHORT
  | USHORT -> USHORT
  | _ ->
      failwith
        (Printf.sprintf "Not a vector type %s" (string_of_if1_basic_ty vect))

and is_vector_type = function
  | Basic ty -> (
      match ty with
      | BYTE2 | BYTE3 | BYTE4 | BYTE8 | BYTE16 | CHAR2 | CHAR3 | CHAR4 | CHAR8
      | CHAR16 | HALF2 | HALF3 | HALF4 | HALF8 | HALF16 | SHORT2 | SHORT3
      | SHORT4 | SHORT8 | SHORT16 | INT2 | INT3 | INT4 | INT8 | INT16 | FLOAT2
      | FLOAT3 | FLOAT4 | FLOAT8 | FLOAT16 | DOUBLE2 | DOUBLE3 | DOUBLE4
      | DOUBLE8 | DOUBLE16 | UBYTE2 | UBYTE3 | UBYTE4 | UBYTE8 | UBYTE16
      | UCHAR2 | UCHAR3 | UCHAR4 | UCHAR8 | UCHAR16 | USHORT2 | USHORT3
      | USHORT4 | USHORT8 | USHORT16 | UINT2 | UINT3 | UINT4 | UINT8 | UINT16
      | LONG2 | LONG3 | LONG4 | LONG8 | LONG16 | ULONG2 | ULONG3 | ULONG4
      | ULONG8 | ULONG16 ->
          true
      | _ -> false)
  | _ -> false

and get_byte_vec_type l =
  match l with
  | 2 -> BYTE2
  | 3 -> BYTE3
  | 4 -> BYTE4
  | 8 -> BYTE8
  | 16 -> BYTE16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for byte can only be 2, 3, 4, 8 or 16, got \
            %d"
           l)

and get_char_vec_type l =
  match l with
  | 2 -> CHAR2
  | 3 -> CHAR3
  | 4 -> CHAR4
  | 8 -> CHAR8
  | 16 -> CHAR16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for char can only be 2, 3, 4, 8 or 16, got \
            %d"
           l)

and get_half_vec_type l =
  match l with
  | 2 -> HALF2
  | 3 -> HALF3
  | 4 -> HALF4
  | 8 -> HALF8
  | 16 -> HALF16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for half can only be 2, 3, 4, 8 or 16, got \
            %d"
           l)

and get_short_vec_type l =
  match l with
  | 2 -> SHORT2
  | 3 -> SHORT3
  | 4 -> SHORT4
  | 8 -> SHORT8
  | 16 -> SHORT16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for short can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_int_vec_type l =
  match l with
  | 2 -> INT2
  | 3 -> INT3
  | 4 -> INT4
  | 8 -> INT8
  | 16 -> INT16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for int can only be 2, 3, 4, 8 or 16, got \
            %d"
           l)

and get_float_vec_type l =
  match l with
  | 2 -> FLOAT2
  | 3 -> FLOAT3
  | 4 -> FLOAT4
  | 8 -> FLOAT8
  | 16 -> FLOAT16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for float can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_double_vec_type l =
  match l with
  | 2 -> DOUBLE2
  | 3 -> DOUBLE3
  | 4 -> DOUBLE4
  | 8 -> DOUBLE8
  | 16 -> DOUBLE16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for double can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_ubyte_vec_type l =
  match l with
  | 2 -> UBYTE2
  | 3 -> UBYTE3
  | 4 -> UBYTE4
  | 8 -> UBYTE8
  | 16 -> UBYTE16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for ubyte can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_uchar_vec_type l =
  match l with
  | 2 -> UCHAR2
  | 3 -> UCHAR3
  | 4 -> UCHAR4
  | 8 -> UCHAR8
  | 16 -> UCHAR16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for uchar can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_ushort_vec_type l =
  match l with
  | 2 -> USHORT2
  | 3 -> USHORT3
  | 4 -> USHORT4
  | 8 -> USHORT8
  | 16 -> USHORT16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for ushort can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_long_vec_type l =
  match l with
  | 2 -> LONG2
  | 3 -> LONG3
  | 4 -> LONG4
  | 8 -> LONG8
  | 16 -> LONG16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for long can only be 2, 3, 4, 8 or 16, got \
            %d"
           l)

and get_uint_vec_type l =
  match l with
  | 2 -> UINT2
  | 3 -> UINT3
  | 4 -> UINT4
  | 8 -> UINT8
  | 16 -> UINT16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for uint can only be 2, 3, 4, 8 or 16, got \
            %d"
           l)

and get_ulong_vec_type l =
  match l with
  | 2 -> ULONG2
  | 3 -> ULONG3
  | 4 -> ULONG4
  | 8 -> ULONG8
  | 16 -> ULONG16
  | _ ->
      failwith
        (Printf.sprintf
           "Type error: vector type for ulong can only be 2, 3, 4, 8 or 16, \
            got %d"
           l)

and get_vec_len tt =
  match tt with
  | BYTE2 | CHAR2 | HALF2 | SHORT2 | INT2 | FLOAT2 | DOUBLE2 | UBYTE2 | UCHAR2
  | LONG2 | ULONG2 | USHORT2 | UINT2 ->
      2
  | BYTE3 | CHAR3 | HALF3 | SHORT3 | INT3 | FLOAT3 | DOUBLE3 | UBYTE3 | UCHAR3
  | LONG3 | ULONG3 | USHORT3 | UINT3 ->
      3
  | BYTE4 | CHAR4 | HALF4 | SHORT4 | INT4 | FLOAT4 | DOUBLE4 | UBYTE4 | UCHAR4
  | LONG4 | ULONG4 | USHORT4 | UINT4 ->
      4
  | BYTE8 | CHAR8 | HALF8 | SHORT8 | INT8 | FLOAT8 | LONG8 | DOUBLE8 | UBYTE8
  | UCHAR8 | ULONG8 | USHORT8 | UINT8 ->
      8
  | BYTE16 | CHAR16 | HALF16 | SHORT16 | INT16 | LONG16 | FLOAT16 | DOUBLE16
  | UBYTE16 | UCHAR16 | USHORT16 | UINT16 | ULONG16 ->
      16
  | _ ->
      failwith
        (Printf.sprintf "Not a vector type: %s for getting vector length"
           (string_of_if1_basic_ty tt))

and build_vector_of_type ty width =
  match ty with
  | Basic b -> Basic (build_vector_of_type_impl width b)
  | _ ->
      failwith
        (Printf.sprintf "Cannot build vector types for Type: %s"
           (string_of_if1_ty ty))

and build_vector_of_type_impl width ty =
  match ty with
  | BYTE -> get_byte_vec_type width
  | CHARACTER -> get_char_vec_type width
  | HALF -> get_half_vec_type width
  | SHORT -> get_short_vec_type width
  | INTEGRAL -> get_int_vec_type width
  | LONG -> get_long_vec_type width
  | REAL -> get_float_vec_type width
  | DOUBLE -> get_double_vec_type width
  | UBYTE -> get_ubyte_vec_type width
  | UCHAR -> get_uchar_vec_type width
  | USHORT -> get_ushort_vec_type width
  | UINT -> get_uint_vec_type width
  | ULONG -> get_ulong_vec_type width
  | _ ->
      failwith
        (Printf.sprintf "Type error: vector type not possible for %s"
           (string_of_if1_basic_ty ty))

and string_of_pair_int (x, y) =
  "(" ^ string_of_int x ^ "," ^ string_of_int y ^ ")"

and safe_set_arr str po arr =
  if Array.length arr < po then (
    arr.(po) <- arr.(po) ^ str;
    arr)
  else Array.of_list (Array.to_list arr @ [ str ])

and set_out_port_str src_nod src_port dest_nn =
  match src_nod with
  | Literal (lab, ty, str, pout) ->
      Literal (lab, ty, str, safe_set_arr dest_nn src_port pout)
  | Simple (lab, n, pin, pout, prag) ->
      Simple (lab, n, pin, safe_set_arr dest_nn src_port pout, prag)
  | Compound (_, _, _, _, _, _) -> src_nod
  | Boundary (_, _, _, _) -> src_nod
  | Unknown_node -> src_nod

and clear_port_str dst_nod =
  match dst_nod with
  | Literal (lab, ty, str, _) ->
      let kk = Array.make 1 "" in
      Literal (lab, ty, str, kk)
  | Simple (lab, n, _, _, prag) ->
      let kk = Array.make 1 "" in
      let ll = Array.make 1 "" in
      Simple (lab, n, kk, ll, prag)
  | Compound (_, _, _, _, _, _) -> dst_nod
  | Boundary _ -> dst_nod
  | Unknown_node -> dst_nod

and set_in_port dst_nod dst_port src_nn =
  match dst_nod with
  | Literal (_, _, _, _) -> dst_nod
  | Simple (lab, n, pin, pout, prag) ->
      if pin.(dst_port) <> "" then raise (Node_not_found "in_port set already")
      else Simple (lab, n, safe_set_arr src_nn dst_port pin, pout, prag)
  | Compound (_, _, _, _, _, _) -> dst_nod
  | Boundary _ -> dst_nod
  | Unknown_node -> dst_nod

and set_in_port_str dst_nod dst_port src_str =
  match dst_nod with
  | Literal (_, _, _, _) -> dst_nod
  | Simple (lab, n, pin, pout, prag) ->
      Simple (lab, n, safe_set_arr src_str dst_port pin, pout, prag)
  | Compound (_, _, _, _, _, _) -> dst_nod
  | Boundary _ -> dst_nod
  | Unknown_node -> dst_nod

and set_literal dst_nod dst_port src_node =
  match src_node with
  | Literal (_, _, str_, _) -> (
      match dst_nod with
      | Literal (_, _, _, _) -> dst_nod
      | Simple (lab, n, pin, pout, prag) ->
          Simple
            ( lab,
              n,
              (pin.(dst_port) <- "Literal:" ^ str_;
               pin),
              pout,
              prag )
      | Compound (_, _, _, _, _, _) -> dst_nod
      | Boundary _ -> dst_nod
      | Unknown_node -> dst_nod)
  | _ -> dst_nod

and add_node nn in_gr =
  let { nmap = nm; eset = _; symtab = par_cs, par_ps; typemap = tm; w = pi } =
    in_gr
  in

  match nn with
  | `Simple (n, pin, pout, prag) ->
      let _ =
        if !Debug.level > 0 then begin
          let stack = Printexc.get_callstack 5 in
          node_trace :=
            (Printf.sprintf "%d" in_gr.w, Printexc.raw_backtrace_to_string stack)
            :: !node_trace
        end
      in
      {
        in_gr with
        nmap = NM.add pi (Simple (pi, n, pin, pout, prag)) nm;
        w = pi + 1;
      }
  | `Compound (g, sy, ty, prag, alis) ->
      let g_tmn = get_types_from_graph g tm in
      let g = { g with typemap = g_tmn } in
      let child_ps = snd (get_symtab g) in
      let par_ps = SM.fold (fun k v z -> SM.add k v z) child_ps par_ps in
      let pi = in_gr.w in
      let in_gr =
        {
          in_gr with
          nmap = NM.add pi (Compound (pi, sy, ty, prag, g, alis)) nm;
          symtab = (par_cs, par_ps);
          typemap = g_tmn;
          w = pi + 1;
        }
      in
      let ipl =
        match get_boundary_node g with Boundary (l, _, _, _) -> List.rev l | _ -> []
      in
      let rec loop idx acc_gr = function
        | [] -> acc_gr
        | (sn, sp, name) :: tl ->
            let ty =
              if SM.mem name par_cs then (SM.find name par_cs).val_ty
              else if SM.mem name par_ps then (SM.find name par_ps).val_ty
              else 0
            in
            if ty <> 0 then
              let acc_gr = add_edge2 sn sp pi idx ty acc_gr in
              loop (idx + 1) acc_gr tl
            else loop (idx + 1) acc_gr tl
      in
      loop 0 in_gr ipl
  | `Literal (ty_lab, str, pout) ->
      {
        in_gr with
        nmap = NM.add pi (Literal (pi, ty_lab, str, pout)) nm;
        symtab = (par_cs, par_ps);
        w = pi + 1;
      }
  | `Boundary ->
      {
        in_gr with
        nmap = NM.add 0 (Boundary ([], [], [], [])) nm;
        symtab = (par_cs, par_ps);
      }

and set_node_srcline node_id line col in_gr =
  let nm = in_gr.nmap in
  match NM.find_opt node_id nm with
  | None -> in_gr
  | Some nd ->
      let nd' =
        match nd with
        | Simple (lab, sym, pin, pout, prag) ->
            Simple (lab, sym, pin, pout, SrcLine (line, col) :: prag)
        | Compound (lab, sym, ty, prag, subgr, assoc) ->
            Compound (lab, sym, ty, SrcLine (line, col) :: prag, subgr, assoc)
        | Literal _ | Boundary _ | Unknown_node -> nd
      in
      { in_gr with nmap = NM.add node_id nd' nm }

and add_name_pragma node_id name in_gr =
  let nm = in_gr.nmap in
  match NM.find_opt node_id nm with
  | None -> in_gr
  | Some nd ->
      let has_name p =
        List.exists (function Name _ -> true | _ -> false) p
      in
      let nd' =
        match nd with
        | Simple (lab, sym, pin, pout, prag) ->
            if has_name prag then nd
            else Simple (lab, sym, pin, pout, Name name :: prag)
        | Compound (lab, sym, ty, prag, subgr, assoc) ->
            if has_name prag then nd
            else Compound (lab, sym, ty, Name name :: prag, subgr, assoc)
        | Literal _ | Boundary _ | Unknown_node -> nd
      in
      { in_gr with nmap = NM.add node_id nd' nm }

and is_real_type gg =
  match gg with
  | Basic _ -> (
      match get_element_type_code gg with
      | REAL | DOUBLE | HALF -> true
      | _ -> false)
  | _ -> false

and is_integral_type gg =
  match gg with
  | Basic _ -> (
      match get_element_type_code gg with
      | BOOLEAN -> true
      | CHARACTER -> true
      | INTEGRAL -> true
      | BYTE -> true
      | UCHAR -> true
      | SHORT -> true
      | USHORT -> true
      | UINT -> true
      | UBYTE -> true
      | LONG -> true
      | ULONG -> true
      | _ -> false)
  | _ -> false

and lookup_tyid = function
  | BOOLEAN -> 1
  | BYTE -> 2
  | CHARACTER -> 3
  | DOUBLE -> 4
  | HALF -> 5
  | INTEGRAL -> 6
  | LONG -> 7
  | REAL -> 8
  | SHORT -> 9
  | UBYTE -> 10
  | UCHAR -> 11
  | UINT -> 12
  | ULONG -> 13
  | USHORT -> 14
  | BYTE2 -> 15
  | CHAR2 -> 16
  | DOUBLE2 -> 17
  | HALF2 -> 18
  | INT2 -> 19
  | LONG2 -> 20
  | FLOAT2 -> 21
  | SHORT2 -> 22
  | UBYTE2 -> 23
  | UCHAR2 -> 24
  | UINT2 -> 25
  | ULONG2 -> 26
  | USHORT2 -> 27
  | BYTE3 -> 28
  | CHAR3 -> 29
  | DOUBLE3 -> 30
  | HALF3 -> 31
  | INT3 -> 32
  | LONG3 -> 33
  | FLOAT3 -> 34
  | SHORT3 -> 35
  | UBYTE3 -> 36
  | UCHAR3 -> 37
  | UINT3 -> 38
  | ULONG3 -> 39
  | USHORT3 -> 40
  | BYTE4 -> 41
  | CHAR4 -> 42
  | DOUBLE4 -> 43
  | HALF4 -> 44
  | INT4 -> 45
  | LONG4 -> 46
  | FLOAT4 -> 47
  | SHORT4 -> 48
  | UBYTE4 -> 49
  | UCHAR4 -> 50
  | UINT4 -> 51
  | ULONG4 -> 52
  | USHORT4 -> 53
  | BYTE8 -> 54
  | CHAR8 -> 55
  | DOUBLE8 -> 56
  | HALF8 -> 57
  | INT8 -> 58
  | LONG8 -> 59
  | FLOAT8 -> 60
  | SHORT8 -> 61
  | UBYTE8 -> 62
  | UCHAR8 -> 63
  | UINT8 -> 64
  | ULONG8 -> 65
  | USHORT8 -> 66
  | BYTE16 -> 67
  | CHAR16 -> 68
  | DOUBLE16 -> 69
  | HALF16 -> 70
  | INT16 -> 71
  | LONG16 -> 72
  | FLOAT16 -> 73
  | SHORT16 -> 74
  | UBYTE16 -> 75
  | UCHAR16 -> 76
  | UINT16 -> 77
  | ULONG16 -> 78
  | USHORT16 -> 79
  | MAT2 -> 80
  | MAT3 -> 81
  | MAT4 -> 82
  | NULL -> 83
  | _ as gg ->
      failwith
        (Printf.sprintf "Can only look up native types with lookup_tyid, not %s"
           (string_of_if1_basic_ty gg))

and short_name_for_intrinsic = function
  | 2 -> "Y"
  | 3 -> "C"
  | 4 -> "D"
  | 5 -> "H"
  | 6 -> "I"
  | 7 -> "L"
  | 8 -> "F"
  | 9 -> "S"
  | 10 -> "UY"
  | 11 -> "UC"
  | 12 -> "UI"
  | 13 -> "UL"
  | 14 -> "US"
  | 15 -> "V2Y"
  | 16 -> "V2C"
  | 17 -> "V2D"
  | 18 -> "V2H"
  | 19 -> "V2I"
  | 20 -> "V2L"
  | 21 -> "V2F"
  | 22 -> "V2S"
  | 23 -> "V2UY"
  | 24 -> "V2UC"
  | 25 -> "V2UI"
  | 26 -> "V2UL"
  | 27 -> "V2US"
  | 28 -> "V3Y"
  | 29 -> "V3C"
  | 30 -> "V3D"
  | 31 -> "V3H"
  | 32 -> "V3I"
  | 33 -> "V3L"
  | 34 -> "V3F"
  | 35 -> "V3S"
  | 36 -> "V3UY"
  | 37 -> "V3UC"
  | 38 -> "V3UI"
  | 39 -> "V3UL"
  | 40 -> "V3US"
  | 41 -> "V4Y"
  | 42 -> "V4C"
  | 43 -> "V4D"
  | 44 -> "V4H"
  | 45 -> "V4I"
  | 46 -> "V4L"
  | 47 -> "V4F"
  | 48 -> "V4S"
  | 49 -> "V4UY"
  | 50 -> "V4UC"
  | 51 -> "V4UI"
  | 52 -> "V4UL"
  | 53 -> "V4US"
  | 54 -> "V8Y"
  | 55 -> "V8C"
  | 56 -> "V8D"
  | 57 -> "V8H"
  | 58 -> "V8I"
  | 59 -> "V8L"
  | 60 -> "V8F"
  | 61 -> "V8S"
  | 62 -> "V8UY"
  | 63 -> "V8UC"
  | 64 -> "V8UI"
  | 65 -> "V8UL"
  | 66 -> "V8US"
  | 67 -> "V16Y"
  | 68 -> "V16C"
  | 69 -> "V16D"
  | 70 -> "V16H"
  | 71 -> "V16I"
  | 72 -> "V16L"
  | 73 -> "V16F"
  | 74 -> "V16S"
  | 75 -> "V16UY"
  | 76 -> "V16UC"
  | 77 -> "V16UI"
  | 78 -> "V16UL"
  | 79 -> "V16US"
  | 80 -> "M2"
  | 81 -> "M3"
  | 82 -> "M4"
  | _ -> "U"

and rev_lookup_ty_name = function
  | 1 -> "BOOLEAN"
  | 2 -> "BYTE"
  | 3 -> "CHARACTER"
  | 4 -> "DOUBLE"
  | 5 -> "HALF"
  | 6 -> "INTEGRAL"
  | 7 -> "LONG"
  | 8 -> "REAL"
  | 9 -> "SHORT"
  | 10 -> "UBYTE"
  | 11 -> "UCHAR"
  | 12 -> "UINT"
  | 13 -> "ULONG"
  | 14 -> "USHORT"
  | 15 -> "BYTE2"
  | 16 -> "CHAR2"
  | 17 -> "DOUBLE2"
  | 18 -> "HALF2"
  | 19 -> "INT2"
  | 20 -> "LONG2"
  | 21 -> "FLOAT2"
  | 22 -> "SHORT2"
  | 23 -> "UBYTE2"
  | 24 -> "UCHAR2"
  | 25 -> "UINT2"
  | 26 -> "ULONG2"
  | 27 -> "USHORT2"
  | 28 -> "BYTE3"
  | 29 -> "CHAR3"
  | 30 -> "DOUBLE3"
  | 31 -> "HALF3"
  | 32 -> "INT3"
  | 33 -> "LONG3"
  | 34 -> "FLOAT3"
  | 35 -> "SHORT3"
  | 36 -> "UBYTE3"
  | 37 -> "UCHAR3"
  | 38 -> "UINT3"
  | 39 -> "ULONG3"
  | 40 -> "USHORT3"
  | 41 -> "BYTE4"
  | 42 -> "CHAR4"
  | 43 -> "DOUBLE4"
  | 44 -> "HALF4"
  | 45 -> "INT4"
  | 46 -> "LONG4"
  | 47 -> "FLOAT4"
  | 48 -> "SHORT4"
  | 49 -> "UBYTE4"
  | 50 -> "UCHAR4"
  | 51 -> "UINT4"
  | 52 -> "ULONG4"
  | 53 -> "USHORT4"
  | 54 -> "BYTE8"
  | 55 -> "CHAR8"
  | 56 -> "DOUBLE8"
  | 57 -> "HALF8"
  | 58 -> "INT8"
  | 59 -> "LONG8"
  | 60 -> "FLOAT8"
  | 61 -> "SHORT8"
  | 62 -> "UBYTE8"
  | 63 -> "UCHAR8"
  | 64 -> "UINT8"
  | 65 -> "ULONG8"
  | 66 -> "USHORT8"
  | 67 -> "BYTE16"
  | 68 -> "CHAR16"
  | 69 -> "DOUBLE16"
  | 70 -> "HALF16"
  | 71 -> "INT16"
  | 72 -> "LONG16"
  | 73 -> "FLOAT16"
  | 74 -> "SHORT16"
  | 75 -> "UBYTE16"
  | 76 -> "UCHAR16"
  | 77 -> "UINT16"
  | 78 -> "ULONG16"
  | 79 -> "USHORT16"
  | 80 -> "MAT2"
  | 81 -> "MAT3"
  | 82 -> "MAT4"
  | 83 -> "NULL"
  | -2 -> "U__NKNOWN"
  | _ -> "UNKNOWN"

and lookup_tyid_triple = function
  | BOOLEAN -> (1, 0, 1)
  | BYTE -> (2, 0, 2)
  | CHARACTER -> (3, 0, 3)
  | DOUBLE -> (4, 0, 4)
  | HALF -> (5, 0, 5)
  | INTEGRAL -> (6, 0, 6)
  | LONG -> (7, 0, 7)
  | REAL -> (8, 0, 8)
  | SHORT -> (9, 0, 9)
  | UBYTE -> (10, 0, 10)
  | UCHAR -> (11, 0, 11)
  | UINT -> (12, 0, 12)
  | ULONG -> (13, 0, 13)
  | USHORT -> (14, 0, 14)
  | BYTE2 -> (15, 0, 15)
  | CHAR2 -> (16, 0, 16)
  | DOUBLE2 -> (17, 0, 17)
  | HALF2 -> (18, 0, 18)
  | INT2 -> (19, 0, 19)
  | LONG2 -> (20, 0, 20)
  | FLOAT2 -> (21, 0, 21)
  | SHORT2 -> (22, 0, 22)
  | UBYTE2 -> (23, 0, 23)
  | UCHAR2 -> (24, 0, 24)
  | UINT2 -> (25, 0, 25)
  | ULONG2 -> (26, 0, 26)
  | USHORT2 -> (27, 0, 27)
  | BYTE3 -> (28, 0, 28)
  | CHAR3 -> (29, 0, 29)
  | DOUBLE3 -> (30, 0, 30)
  | HALF3 -> (31, 0, 31)
  | INT3 -> (32, 0, 32)
  | LONG3 -> (33, 0, 33)
  | FLOAT3 -> (34, 0, 34)
  | SHORT3 -> (35, 0, 35)
  | UBYTE3 -> (36, 0, 36)
  | UCHAR3 -> (37, 0, 37)
  | UINT3 -> (38, 0, 38)
  | ULONG3 -> (39, 0, 39)
  | USHORT3 -> (40, 0, 40)
  | BYTE4 -> (41, 0, 41)
  | CHAR4 -> (42, 0, 42)
  | DOUBLE4 -> (43, 0, 43)
  | HALF4 -> (44, 0, 44)
  | INT4 -> (45, 0, 45)
  | LONG4 -> (46, 0, 46)
  | FLOAT4 -> (47, 0, 47)
  | SHORT4 -> (48, 0, 48)
  | UBYTE4 -> (49, 0, 49)
  | UCHAR4 -> (50, 0, 50)
  | UINT4 -> (51, 0, 51)
  | ULONG4 -> (52, 0, 52)
  | USHORT4 -> (53, 0, 53)
  | BYTE8 -> (54, 0, 54)
  | CHAR8 -> (55, 0, 55)
  | DOUBLE8 -> (56, 0, 56)
  | HALF8 -> (57, 0, 57)
  | INT8 -> (58, 0, 58)
  | LONG8 -> (59, 0, 59)
  | FLOAT8 -> (60, 0, 60)
  | SHORT8 -> (61, 0, 61)
  | UBYTE8 -> (62, 0, 62)
  | UCHAR8 -> (63, 0, 63)
  | UINT8 -> (64, 0, 64)
  | ULONG8 -> (65, 0, 65)
  | USHORT8 -> (66, 0, 66)
  | BYTE16 -> (67, 0, 67)
  | CHAR16 -> (68, 0, 68)
  | DOUBLE16 -> (69, 0, 69)
  | HALF16 -> (70, 0, 70)
  | INT16 -> (71, 0, 71)
  | LONG16 -> (72, 0, 72)
  | FLOAT16 -> (73, 0, 73)
  | SHORT16 -> (74, 0, 74)
  | UBYTE16 -> (75, 0, 75)
  | UCHAR16 -> (76, 0, 76)
  | UINT16 -> (77, 0, 77)
  | ULONG16 -> (78, 0, 78)
  | USHORT16 -> (79, 0, 79)
  | MAT2 -> (80, 0, 80)
  | MAT3 -> (81, 0, 81)
  | MAT4 -> (82, 0, 82)
  | NULL -> (83, 0, 83)
  | _ as f ->
      failwith
        (Printf.sprintf "Can only look up native types with lookup_tyid, not %s"
           (string_of_if1_basic_ty f))

and find_sym_opt val_name in_gr =
  let cs, ps = get_symtab in_gr in
  match SM.find_opt val_name cs with
  | None -> SM.find_opt val_name ps
  | _ as re -> re

and fold_ret_ty_lis ret_ty tm =
  match TM.find_opt ret_ty tm with
  | Some (Tuple_ty (fty, nty)) ->
      if nty = 0 then [ fty ] else fty :: fold_ret_ty_lis nty tm
  | _ -> failwith "Incorrect function type in"

and lookup_fn_ty in_fn_name in_gr =
  (* this looks at the typemap table and return type
   * for an id - this can do that in the local and the global
   * ty tabs just like symtab does *)
  let tm = get_typemap_tm in_gr in
  let { val_name = _; val_ty = sym_ty; val_def = _; def_port = _ } =
    match find_sym_opt in_fn_name in_gr with
    | Some reco -> reco
    | None -> failwith ("FUNCTION NOT FOUND: " ^ in_fn_name)
  in
  match TM.find_opt sym_ty tm with
  | Some tt -> (
      match tt with
      | Function_ty (_, ret_ty, _) -> fold_ret_ty_lis ret_ty tm
      | _ -> failwith "Type does not resolve to function")
  | _ -> failwith "Type not found"

and propagate_error_ports inner_gr compound_node_id outer_gr =
  let inner_boundary = NM.find 0 inner_gr.nmap in
  match inner_boundary with
  | Boundary (_, _, inner_errs, _) ->
      (* Linear fold ensures every inner error gets a unique outer port *)
      List.fold_left
        (fun current_outer_gr (_, err_ty) ->
          match NM.find 0 current_outer_gr.nmap with
          | Boundary (ins, outs, outer_errs, prags) ->
              let next_err_port = List.length outer_errs in

              (* 1. Lift the error metadata to the parent boundary *)
              let updated_boundary =
                Boundary
                  (ins, outs, outer_errs @ [ (compound_node_id, err_ty) ], prags)
              in
              let outer_gr_updated =
                {
                  current_outer_gr with
                  nmap = NM.add 0 updated_boundary current_outer_gr.nmap;
                }
              in

              (* 2. Wire Compound:ErrPort[N] -> Boundary:ErrPort[N] *)
              add_edge2 compound_node_id next_err_port 0 next_err_port err_ty
                outer_gr_updated
          | _ -> current_outer_gr)
        outer_gr inner_errs
  | _ -> outer_gr

and add_node_2 nn in_gr =
  let nm = get_node_map in_gr in
  let pi = get_graph_label in_gr in
  let tm = get_typemap in_gr in
  match nn with
  | `Simple (n, pin, pout, prag) ->
      ( (pi, 0, 0),
        {
          in_gr with
          nmap = NM.add pi (Simple (pi, n, pin, pout, prag)) nm;
          w = pi + 1;
        } )
  | `Compound (g, sy, ty, prag, alis) ->
      let g_tmn = get_types_from_graph g tm in
      let g = { g with typemap = g_tmn } in
      let base_gr =
        {
          in_gr with
          nmap = NM.add pi (Compound (pi, sy, ty, prag, g, alis)) nm;
          typemap = g_tmn;
          w = pi + 1;
        }
      in
      ((pi, 0, 0), propagate_error_ports g pi base_gr)
  | `Literal (ty_lab, str, pout) ->
      ( (pi, 0, lookup_tyid ty_lab),
        {
          in_gr with
          nmap = NM.add pi (Literal (pi, ty_lab, str, pout)) nm;
          w = pi + 1;
        } )
  | `Boundary ->
      ( (pi, 0, 0),
        {
          in_gr with
          nmap = NM.add 0 (Boundary ([], [], [], [])) nm;
          w = pi + 1;
        } )

and add_edge2 n1 p1 n2 p2 ed_ty in_gr =
  let nm = get_node_map in_gr in
  let _ =
    match NM.find_opt n2 nm with
    | Some (Simple (_, _, pin, _, _)) ->
        if p2 >= 0 && p2 < Array.length pin then pin.(p2) <- string_of_int n1
    | _ -> ()
  in
  let _ =
    match NM.find_opt n1 nm with
    | Some (Simple (_, _, _, pout, _)) ->
        if p1 >= 0 && p1 < Array.length pout then
          pout.(p1) <- cate_nicer pout.(p1) (string_of_int n2) ","
    | Some (Literal (_, _, _, pout)) ->
        if p1 >= 0 && p1 < Array.length pout then
          pout.(p1) <- cate_nicer pout.(p1) (string_of_int n2) ","
    | _ -> ()
  in
  let pe = get_edge_set in_gr in
  (* Trace boundary edges (to Node 0) to debug Return Mismatches *)
  let _ =
    if !Debug.level > 0 then begin
      let stack = get_stack_trace 5 in
      let ty_desc =
        "(#" ^ string_of_int ed_ty ^ "): "
        ^ printable_full_type (get_typemap_tm in_gr) ed_ty
      in
      if n2 = 0 || n1 = 0 then ()
      else
        let dest_str = string_of_node n2 in_gr in
        let src_str = string_of_node n1 in_gr in
        edge_trace :=
          ( Printf.sprintf "%d[%s]P:%d" n1 src_str p1,
            Printf.sprintf "%d[%s]P:%d" n2 dest_str p2,
            ty_desc,
            stack )
          :: !edge_trace
    end
  in
  { in_gr with eset = ES.add ((n1, p1), (n2, p2), ed_ty) pe }

and fix_incoming_multiarity n1 p1 n2 p2 aty in_gr =
  let nm, pe = get_node_map_and_edge_set in_gr in
  match NM.find_opt n1 nm with
  | Some (Simple (_, MULTIARITY, _, _, _)) ->
      let ending_at = all_edges_ending_at_port n1 p1 in_gr in
      let nes =
        if ES.cardinal ending_at <> 1 then
          raise
            (Sem_error
               (">1 incoming found in multiarity"
              ^ " - all fan-ins must be exactly 1 or 0"))
        else
          let nending_at =
            ES.fold
              (fun ((x, xp), (_, _), y_ty) res ->
                ES.add ((x, xp), (n2, p2), y_ty) res)
              ending_at ES.empty
          in
          ES.union (ES.remove ((n1, p1), (n2, p2), aty) pe) nending_at
      in
      { in_gr with eset = nes }
  | Some _ -> in_gr
  | None -> failwith "Exception node not found in fix_incoming_multiarity"

and all_edges n1 n2 in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((x, _), (y, _), _) -> x = n1 && y = n2) pe in
  edges

and all_edges_ending_at_port n2 p2 in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((_, _), (y, yp), _) -> y = n2 && yp = p2) pe in
  edges

and all_edges_ending_at n2 in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((_, _), (y, _), _) -> y = n2) pe in
  edges

and all_edges_ending_at_ports_types n2 in_gr =
  let pe = get_edge_set in_gr in
  let edges =
    ES.filter
      (fun ((_, _), (y, _), ty) -> y = n2 && not (is_error_port ty in_gr))
      pe
  in
  ES.fold (fun ((_, _), (_, yp), y_ty) z -> (yp, y_ty) :: z) edges []

and all_nodes_joining_at (n2, _, _) in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((_, _), (y, _), _) -> y = n2) pe in
  List.fold_right
    (fun ((x, xp), (_, _), y_ty) zz -> (x, xp, y_ty) :: zz)
    (ES.elements edges) []

and all_nodes_incoming n2 in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((_, _), (y, _), _) -> y = n2) pe in
  List.fold_right
    (fun ((x, xp), (_, _), y_ty) zz -> (x, xp, y_ty) :: zz)
    (ES.elements edges) []

and all_types_ending_at_no_err_ty n2 in_gr res =
  let pe = get_edge_set in_gr in
  let map_tnem =
    ES.fold
      (fun ((_, _), (y, yp), y_ty) acc ->
        if y = n2 && not (is_error_port y_ty in_gr) then IntMap.add yp y_ty acc
        else acc)
      pe res
  in
  map_tnem

and is_typed_error_port ty_id in_gr =
  let _, tm, _ = get_typemap in_gr in
  match TM.find_opt ty_id tm with Some (ERROR _) -> true | _ -> false

and is_error_port ty_id in_gr =
  let _, tm, _ = get_typemap in_gr in
  match TM.find_opt ty_id tm with Some (ERROR _) -> true | _ -> false

and is_typed_error_ty ty_id in_gr =
  let _, tm, _ = get_typemap in_gr in
  match TM.find_opt ty_id tm with Some (Typed_error _) -> true | _ -> false

and type_of_error_ty ty_id in_gr =
  let _, tm, _ = get_typemap in_gr in
  match TM.find_opt ty_id tm with
  | Some (Typed_error xy) -> xy
  | _ ->
      failwith
        ("Excepted Typed error type, but got "
        ^ printable_full_type tm ty_id
        ^ "\n")

and connect_one_to_one in_lis to_n in_gr =
  let in_gr, _ =
    List.fold_right
      (fun (n1, p1, y_ty) (zzz, p2) ->
        (add_edge n1 p1 to_n (p2 + 1) y_ty zzz, p2 + 1))
      in_lis (in_gr, 0)
  in
  in_gr

and all_edges_starting_at n1 in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((x, _), (_, _), _) -> x = n1) pe in
  edges

and check_for_multiarity n1 n2 in_gr =
  let nm = get_node_map in_gr in
  match NM.find_opt n1 nm with
  | Some (Simple (_, MULTIARITY, _, _, _)) -> (
      match NM.find_opt n2 nm with
      | Some (Simple (_, MULTIARITY, _, _, _)) -> true
      | Some _ -> false
      | None ->
          failwith
            ("Exception in check_for_multiarity on Node " ^ string_of_int n2))
  | Some _ -> false
  | None ->
      failwith
        ("Exception in check_for_multiarity Node not found " ^ string_of_int n1)

and cleanup_multiarity in_gr =
  let { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } = in_gr in
  let new_nm =
    NM.fold
      (fun x y z ->
        match y with
        | Simple (_, MULTIARITY, _, _, _) -> z
        | Compound (pi, sy, ty, prag, g, alis) ->
            NM.add x (Compound (pi, sy, ty, prag, cleanup_multiarity g, alis)) z
        | _ -> NM.add x y z)
      nm NM.empty
  in
  let new_edges =
    (* CRITICAL FIX: Check both source (x) AND destination (y) *)
    ES.filter (fun ((x, _), (y, _), _) -> NM.mem x new_nm && NM.mem y new_nm) es
  in
  { nmap = new_nm; eset = new_edges; symtab = sm; typemap = tm; w = pi }

and add_from_edge ((n1, p1), (n2, p2), ed_ty) in_gr =
  add_edge n1 p1 n2 p2 ed_ty in_gr

and node_incoming_at_port n1 p in_gr =
  let edges = ES.elements (all_edges_ending_at_port n1 p in_gr) in
  if List.length edges > 1 then
    raise (Sem_error "Only one fan-in rule being violated")
  else
    try
      let (x, y), (_, _), ty = List.hd edges in
      (x, y, ty)
    with _ ->
      write_any_dot_file "ERROR.dot" in_gr;
      print_string "Error when looking up node incoming to port";
      print_int p;
      print_char '\n';
      print_endline (string_of_graph in_gr);
      Printexc.print_raw_backtrace stdout (Printexc.get_callstack 20);
      raise
        (Sem_error
           ("Failing with node incoming at port:" ^ string_of_int n1 ^ ","
          ^ string_of_int p))

and find_incoming_regular_node (n1, p1, ed_ty) in_gr =
  match get_node n1 in_gr with
  | Simple (_, MULTIARITY, _, _, _) ->
      let n1, p1, ed_ty = node_incoming_at_port n1 p1 in_gr in
      find_incoming_regular_node (n1, p1, ed_ty) in_gr
  | _ -> (n1, p1, ed_ty)

and inject_vouchers_into_symtab in_gr usings =
  let globals, locals = in_gr.symtab in

  let updated_globals =
    List.fold_left
      (fun acc (path, alias_opt) ->
        (* 1. Determine the 'Handle' (The name used in the code) *)
        let handle =
          match alias_opt with
          | Some a -> a (* e.g., 'M' from USING "math" AS M *)
          | None -> path (* e.g., "math.sis" from USING "math.sis" *)
        in

        (* 2. Create the "Ominous" Proxy String (Our Voucher)
       Format: LINK#<path>#<member>#AS#<alias>
       We use '*' for the member to mean 'Full File Access' for now. *)
        let proxy = "LINK#" ^ path ^ "#*#AS#" ^ handle in

        (* 3. Build the val_info record with our -1 Sentinel *)
        let info =
          {
            val_name = proxy;
            val_ty = 0;
            (* Unknown_ty: Resolved during 'Redemption' *)
            val_def = -1;
            (* Our Sentinel: "I am a Voucher" *)
            def_port = 0;
          }
        in

        (* 4. Shadowing: SM.add replaces any existing entry for 'handle' *)
        SM.add handle info acc)
      globals usings
  in

  { in_gr with symtab = (updated_globals, locals) }

and add_edge n1 p1 n2 p2 ed_ty in_gr =
  let _ =
    if !Debug.level > 0 then begin
      let stack = get_stack_trace 5 in
      let ty_desc =
        "(#" ^ string_of_int ed_ty ^ "): "
        ^ printable_full_type (get_typemap_tm in_gr) ed_ty
      in
      let dest_str = string_of_node n2 in_gr in
      let src_str = string_of_node n1 in_gr in
      edge_trace :=
        ( Printf.sprintf "%d[%s]P:%d" n1 src_str p1,
          Printf.sprintf "%d[%s]P:%d" n2 dest_str p2,
          ty_desc,
          stack )
        :: !edge_trace
    end
  in
  let n1, p1, ed_ty = find_incoming_regular_node (n1, p1, ed_ty) in_gr in
  if n2 = 0 then add_to_boundary_outputs ~start_port:p2 n1 p1 ed_ty in_gr
  else
    let in_gr =
      if n1 = 0 then
        let _, in_gr = add_to_boundary_inputs 0 p1 in_gr in
        in_gr
      else in_gr
    in
    let in_gr = add_edge2 n1 p1 n2 p2 ed_ty in_gr in
    in_gr

and redirect_edges n2 es start_port =
  ES.fold
    (fun hde (res, start_port) ->
      let (x, xp), (_, yp), yt = hde in
      (ES.add ((x, xp), (n2, start_port + yp), yt) res, start_port))
    es (ES.empty, start_port)

and incoming_arity n1 in_gr =
  let edges = all_edges_ending_at n1 in_gr in
  ES.cardinal edges

and outgoing_arity n1 in_gr =
  let edges = all_edges_starting_at n1 in_gr in
  ES.cardinal edges

and filter_data_edges in_gr =
  ES.filter (fun ((_, _), (_, _), ty_id) -> not (is_error_port ty_id in_gr))

and fold_multiarity_edge n1 n2 in_gr =
  let edges = all_edges n1 n2 in_gr in
  let ending_at = all_edges_ending_at n1 in_gr in
  let existing_in_edges_n2 =
    filter_data_edges in_gr (all_edges_ending_at n2 in_gr)
  in
  let redir_set, _ =
    redirect_edges n2 (ES.diff ending_at edges)
      (ES.cardinal existing_in_edges_n2)
  in
  let { nmap = _; eset = _; symtab = _; typemap = _; w = _ } = in_gr in
  let { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } =
    ES.fold
      (fun ((x, xp), (y, yp), yt) gr -> add_edge x xp y yp yt gr)
      redir_set in_gr
  in
  let es = ES.diff (ES.diff es ending_at) edges in
  let in_gr = { nmap = nm; eset = es; symtab = sm; typemap = tm; w = pi } in
  in_gr

and add_each_in_list in_gr ex lasti appl =
  match ex with
  | [] -> ((lasti, 0, 0), in_gr)
  | hde :: tl ->
      let (lasti, _, _), in_gr_ = appl in_gr hde in
      add_each_in_list in_gr_ tl lasti appl

and is_multiarity nodenum in_gr =
  match get_node nodenum in_gr with
  | Simple (_, MULTIARITY, _, _, _) -> true
  | _ -> false

and range a b = if a >= b then [] else a :: range (a + 1) b

and incoming_type_at_port n2 p2 in_gr =
  let pe = get_edge_set in_gr in
  let edges = ES.filter (fun ((_, _), (y, yp), _) -> y = n2 && yp = p2) pe in

  match ES.cardinal edges with
  | 0 -> None
  | 1 ->
      let _, _, ty_id = ES.choose edges in
      Some ty_id
  | _ ->
      failwith
        (Printf.sprintf
           "Fan-in violation: Multiple types reaching Node %d Port %d" n2 p2)

and add_each_in_list_to_node olis in_gr ex out_e ni appl =
  match ex with
  | [] -> (olis, in_gr)
  | hde :: tl ->
      let (lasti, pp, tt1), in_gr_ = appl in_gr hde in
      let in_gr_ = add_edge_multiarity lasti pp out_e ni tt1 in_gr_ in
      (* REFINED WIDTH: Check how many ports were actually wired forward *)
      let width =
        if is_multiarity lasti in_gr_ then
          ES.cardinal (all_edges_ending_at lasti in_gr_)
        else 1
      in

      add_each_in_list_to_node ((lasti, pp, tt1) :: olis) in_gr_ tl out_e
        (ni + width) appl

and map_exp in_gr in_explist expl appl =
  match in_explist with
  | [] -> (expl, in_gr)
  | hde :: tl ->
      let (lasti, pp, tt), in_gr = appl in_gr hde in
      map_exp in_gr tl (expl @ [ (lasti, pp, tt) ]) appl

and add_edge_multiarity in_n in_p out_n out_p tt1 in_gr =
  match get_node in_n in_gr with
  | Simple (_, MULTIARITY, _, _, _) ->
      let ll = range 0 (ES.cardinal (all_edges_ending_at in_n in_gr)) in
      (* Use fold_left for naturally ordered port assignment *)
      List.fold_left
        (fun igr x ->
          let inc_type =
            match incoming_type_at_port in_n x igr with
            | Some typ -> typ
            | None ->
                failwith
                  ("Type stall: missing type at MULTIARITY port "
                 ^ string_of_int x)
          in
          let igr = add_edge in_n x out_n (out_p + x) inc_type igr in
          igr)
        in_gr ll
  | _ -> add_edge in_n in_p out_n out_p tt1 in_gr

and get_types_from_graph g inc_blob =
  let g_ty_idx, g_tm, g_tmn =
    let { nmap = _; eset = _; symtab = _; typemap = tyblob; w = _ } = g in
    tyblob
  in
  let inc_blob_ty_idx, inc_block_tm, inc_blob_tmn = inc_blob in

  let out_ty_idx =
    if g_ty_idx >= inc_blob_ty_idx then g_ty_idx else inc_blob_ty_idx
  in
  let merge_fn =
   fun _ xo yo ->
    match (xo, yo) with
    | Some x, Some _ -> Some x
    | None, yo -> yo
    | xo, None -> xo
  in
  let out_tm = TM.merge merge_fn g_tm inc_block_tm in
  let out_tmn = MM.merge merge_fn g_tmn inc_blob_tmn in
  (out_ty_idx, out_tm, out_tmn)

and get_merged_typeblob_gr g1 g2 =
  let g_ty_idx, g_tm, g_tmn = get_typemap g1 in
  let inc_blob_ty_idx, inc_block_tm, inc_blob_tmn = get_typemap g2 in
  let out_ty_idx =
    if g_ty_idx >= inc_blob_ty_idx then g_ty_idx else inc_blob_ty_idx
  in
  let merge_fn =
   fun _ xo yo ->
    match (xo, yo) with
    | Some x, Some _ -> Some x
    | None, yo -> yo
    | xo, None -> xo
  in
  let out_tm = TM.merge merge_fn g_tm inc_block_tm in
  let out_tmn = MM.merge merge_fn g_tmn inc_blob_tmn in
  (out_ty_idx, out_tm, out_tmn)

and merge_typeblobs tyblob1 tyblob2 =
  let g_ty_idx, g_tm, g_tmn = tyblob1 in
  let inc_blob_ty_idx, inc_block_tm, inc_blob_tmn = tyblob2 in
  let out_ty_idx =
    if g_ty_idx >= inc_blob_ty_idx then g_ty_idx else inc_blob_ty_idx
  in
  let merge_fn =
   fun _ xo yo ->
    match (xo, yo) with
    | Some x, Some _ -> Some x
    | None, yo -> yo
    | xo, None -> xo
  in
  let out_tm = TM.merge merge_fn g_tm inc_block_tm in
  let out_tmn = MM.merge merge_fn g_tmn inc_blob_tmn in
  (out_ty_idx, out_tm, out_tmn)

and add_type_to_typemap ood in_gr =
  let id, tm, tmn = get_typemap in_gr in
  if !Debug.level > 0 then begin
    let stack = get_stack_trace 5 in
    let desc = string_of_if1_ty ood in
    type_trace := (id, desc, stack) :: !type_trace
  end;
  ((id, 0, id), { in_gr with typemap = (id + 1, TM.add id ood tm, tmn) })

and add_type_to_typemap_dedup ood in_gr =
  match find_ty_safe_opt in_gr ood with
  | Some existing_id -> ((existing_id, 0, existing_id), in_gr)
  | None -> add_type_to_typemap ood in_gr

and change_type_in_typemap idI ood in_gr =
  let id, tm, tmn = get_typemap in_gr in
  ((id, 0, id), { in_gr with typemap = (id, TM.add idI ood tm, tmn) })

and add_a_tag (namen, tagty, _) ((id, _, _), in_gr) =
  let (tt_id, _, _), in_gr = add_sisal_type in_gr tagty in
  add_type_to_typemap_dedup (Union (tt_id, id, namen)) in_gr

and add_a_field (namen, tagty, _) ((id, _, _), in_gr) =
  let (tt_id, _, _), in_gr = add_sisal_type in_gr tagty in
  add_type_to_typemap_dedup (Record (tt_id, id, namen)) in_gr

and add_tag_spec (strlis, tl, _) in_gr = ((strlis, tl, 0), in_gr)

and add_a_tuple_entry tup_ty ((id, _, _), in_gr) =
  let (tt_id, _, _), in_gr = add_sisal_type in_gr tup_ty in
  add_type_to_typemap (Tuple_ty (tt_id, id)) in_gr

and add_compound_type in_gr = function
  | Sisal_array s ->
      let (iii, _, _), in_gr = add_sisal_type in_gr s in
      add_type_to_typemap_dedup (Array_ty iii) in_gr
  | Sisal_dv s ->
      let (iii, _, _), in_gr = add_sisal_type in_gr s in
      add_type_to_typemap_dedup (Array_dv iii) in_gr
  | Sisal_stream s ->
      let (iii, _, _), in_gr = add_sisal_type in_gr s in
      add_type_to_typemap_dedup (Stream iii) in_gr
  | Sisal_union union_field_and_type_list ->
      let (tag_fst, _, _), in_gr =
        List.fold_right
          (fun (tag_names_l, tag_ty) y ->
            List.fold_right add_a_tag
              (List.map (fun namen -> (namen, tag_ty, 0)) tag_names_l)
              y)
          union_field_and_type_list
          ((0, 0, 0), in_gr)
      in
      add_type_to_typemap_dedup (Union (0, tag_fst, "")) in_gr
  | Sisal_record record_field_and_type_list ->
      let (rec_fst, _, _), in_gr =
        List.fold_right
          (fun (rec_names_l, rec_ty) y ->
            List.fold_right add_a_field
              (List.map (fun namen -> (namen, rec_ty, 0)) rec_names_l)
              y)
          record_field_and_type_list
          ((0, 0, 0), in_gr)
      in
      add_type_to_typemap_dedup (Record (0, rec_fst, "")) in_gr
  | Sisal_function_type (fn_name, tyargs, tyres) ->
      let (res_fst, _, _), in_gr =
        List.fold_right
          (fun curr_t out_stf -> add_a_tuple_entry curr_t out_stf)
          tyres
          ((0, 0, 0), in_gr)
      in
      let (arg_fst, _, _), in_gr =
        List.fold_right
          (fun curr_t out_stf -> add_a_tuple_entry curr_t out_stf)
          tyargs
          ((0, 0, 0), in_gr)
      in
      add_type_to_typemap_dedup (Function_ty (arg_fst, res_fst, fn_name)) in_gr
  | Sisal_tuple type_list ->
      let (tup_fst, _, _), in_gr =
        List.fold_right
          (fun curr_t out_stf -> add_a_tuple_entry curr_t out_stf)
          type_list
          ((0, 0, 0), in_gr)
      in
      ((tup_fst, 0, tup_fst), in_gr)
  | _ -> raise (Node_not_found "In compound type")

(* --------------------------------------------------------------------------
   Dope-vector type: array[{lo:int, stride:int, size:int}]

   Built lazily the first time it is needed and de-duplicated in the typemap.
   The Record chain is built from tail → head so the fields appear in the
   natural order lo/stride/size when printed.
   -------------------------------------------------------------------------- *)

and ensure_dope_vec_type in_gr =
  let int_id = lookup_tyid INTEGRAL in
  (* tail field: size *)
  let (id_size, _, _), in_gr =
    add_type_to_typemap_dedup (Record (int_id, 0, "size")) in_gr
  in
  (* middle field: stride → size *)
  let (id_stride, _, _), in_gr =
    add_type_to_typemap_dedup (Record (int_id, id_size, "stride")) in_gr
  in
  (* head field: lo → stride → size *)
  let (id_lo, _, _), in_gr =
    add_type_to_typemap_dedup (Record (int_id, id_stride, "lo")) in_gr
  in
  (* array[{lo, stride, size}] *)
  let (dope_ty, _, _), in_gr =
    add_type_to_typemap_dedup (Array_ty id_lo) in_gr
  in
  (dope_ty, in_gr)

(* --------------------------------------------------------------------------
   Graph traversal: find the node that actually owns the backing store for an
   array value flowing on edge (n, p).

   Rules:
   - DV view nodes (ROTATE, REVERSE, SLICE, PERMUTE, RESHAPE, COMPRESS,
     GATHER) are transparent — the data lives in their first input.
   - GET_DOPE_VEC port 1 is also transparent (it passes the array through).
   - Any other node is an allocation site: return it.
   - Hitting the graph boundary (node 0) or an IF compound node means the
     data source is ambiguous; raise a meaningful Sem_error.
   -------------------------------------------------------------------------- *)

and find_array_data_source (n, p) in_gr =
  (* DV view nodes are zero-copy: the backing store is their port-0 input. *)
  let dv_transparent =
    [ DV_ROTATE; DV_REVERSE; DV_SLICE; DV_PERMUTE; DV_RESHAPE; DV_COMPRESS;
      DV_GATHER ]
  in
  if n = 0 then
    raise
      (Sem_error
         "find_array_data_source: reached graph boundary — data source \
          unknown (array is a function parameter or crossed an IF merge)")
  else
    match get_node n in_gr with
    | Simple (_, sym, _, _, _) when List.mem sym dv_transparent ->
        (* Traverse through the view node to its source array (port 0 input). *)
        let src_n, src_p, _ = node_incoming_at_port n 0 in_gr in
        find_array_data_source (src_n, src_p) in_gr
    | Simple (_, GET_DOPE_VEC, _, _, _) when p = 1 ->
        (* Port 1 of GET_DOPE_VEC is the array passthrough; follow port 0. *)
        let src_n, src_p, _ = node_incoming_at_port n 0 in_gr in
        find_array_data_source (src_n, src_p) in_gr
    | _ ->
        (* Allocation site (forall, for_initial, literal, compound, etc.). *)
        (n, p)

(* Helper to unroll Tuple_ty chains into a list of strings *)

and string_of_if1_ty_recursive tm seen ty =
  match ty with
  | Basic _ | Multiple _ | ERROR _ | Unknown_ty ->
      (* Leaf items: use your existing printer *)
      string_of_if1_ty ty
  | Typed_error l -> "ERROR [" ^ resolve_and_print tm seen l ^ "]"
  | Array_ty l -> "array[" ^ resolve_and_print tm seen l ^ "]"
  | Array_dv l ->
      "array_dv[" ^ resolve_and_print tm seen l ^ "]"
  | Stream l -> "stream[" ^ resolve_and_print tm seen l ^ "]"
  | Tuple_ty (l1, l2) ->
      if l2 = 0 then "(" ^ resolve_and_print tm seen l1 ^ ")"
      else
        "("
        ^ resolve_and_print tm seen l1
        ^ " * "
        ^ resolve_and_print tm seen l2
        ^ ")"
  (* Updated Function_ty case in your string_of_if1_ty *)
  | Function_ty (input_l, output_l, name) ->
      (* Helper to unroll Tuple_ty chains into a list of strings *)
      let rec flatten_tuple tm seen label =
        if label <> 0 then
          match TM.find_opt label tm with
          | Some (Tuple_ty (current, next)) ->
              let current_str = resolve_and_print tm seen current in
              current_str :: flatten_tuple tm seen next
          | Some _ ->
              [ resolve_and_print tm seen label ] (* Base case: not a tuple *)
          | None -> [ "UNKNOWN" ]
        else []
      in

      let inputs = flatten_tuple tm seen input_l in
      let outputs = flatten_tuple tm seen output_l in
      sprintf "FUNCTION %s (%s) RETURNS (%s)"
        (String.uppercase_ascii name)
        (String.concat ", " inputs)
        (String.concat ", " outputs)
  | Record (field_l, _, name) ->
      let name_str = if name = "" then "" else name ^ " " in
      name_str ^ "record{" ^ resolve_and_print tm seen field_l ^ "}"
  | Field labels ->
      let inner = List.map (resolve_and_print tm seen) labels in
      String.concat "; " inner
  | Tag labels ->
      let inner = List.map (resolve_and_print tm seen) labels in
      "union{" ^ String.concat " | " inner ^ "}"
  | Union (tag_l, _, name) ->
      let name_str = if name = "" then "" else name ^ " " in
      name_str ^ "union{" ^ resolve_and_print tm seen tag_l ^ "}"
  | If1Type_name l -> "alias(" ^ resolve_and_print tm seen l ^ ")"

and resolve_and_print tm seen id =
  (* Cycle Detection: If we've seen this ID in the current branch, just print the ID *)
  if List.mem id seen then "REC_ID:" ^ string_of_int id
  else
    match TM.find_opt id tm with
    | Some ty -> string_of_if1_ty_recursive tm (id :: seen) ty
    | None -> "MISSING_ID:" ^ string_of_int id

and printable_full_type tm id = resolve_and_print tm [] id
and p_f_t in_gr = printable_full_type (get_typemap_tm in_gr)

(* seen: (int * int) list *)
and structurally_equal in_gr seen t1 t2 =
  match (t1, t2) with
  (* --- The Error Monad Guard --- *)
  | Typed_error t1, Typed_error t2 -> t1 = t2
  | ERROR s1, ERROR s2 -> s1 = s2
  | ERROR _, _ | _, ERROR _ -> false
  (* --- Standard Structural Matching --- *)
  | Basic b1, Basic b2 -> b1 = b2
  | Array_ty l1, Array_ty l2 -> resolve_and_compare in_gr seen l1 l2
  | Array_dv l1, Array_dv l2 ->
      resolve_and_compare in_gr seen l1 l2
  | Tuple_ty (l1_a, l1_b), Tuple_ty (l2_a, l2_b) ->
      resolve_and_compare in_gr seen l1_a l2_a
      && resolve_and_compare in_gr seen l1_b l2_b
  | Record (f1, n1, fn1), Record (f2, n2, fn2) ->
      let fs, sn, tr =
        ( resolve_and_compare in_gr seen f1 f2,
          resolve_and_compare in_gr seen n1 n2,
          String.equal fn1 fn2 )
      in
      fs && sn && tr
  | Field labels1, Field labels2 ->
      if List.length labels1 <> List.length labels2 then false
      else
        List.for_all2
          (fun l1 l2 -> resolve_and_compare in_gr seen l1 l2)
          labels1 labels2
  | Function_ty (in1, out1, _), Function_ty (in2, out2, _) ->
      resolve_and_compare in_gr seen in1 in2
      && resolve_and_compare in_gr seen out1 out2
  | Multiple b1, Multiple b2 -> b1 = b2
  | Stream l1, Stream l2 -> resolve_and_compare in_gr seen l1 l2
  | Union (f1, n1, fn1), Union (f2, n2, fn2) ->
      resolve_and_compare in_gr seen f1 f2
      && resolve_and_compare in_gr seen n1 n2
      && String.equal fn1 fn2
  | Tag labels1, Tag labels2 ->
      if List.length labels1 <> List.length labels2 then false
      else
        List.for_all2
          (fun l1 l2 -> resolve_and_compare in_gr seen l1 l2)
          labels1 labels2
  | If1Type_name l1, If1Type_name l2 -> resolve_and_compare in_gr seen l1 l2
  | Unknown_ty, Unknown_ty -> true
  | _, _ -> false

and resolve_and_compare in_gr seen id1 id2 =
  (* If we've already compared these two labels in this recursion branch,
     we've hit a cycle (like a recursive Record). Assume they match. *)
  if List.exists (fun (l1, l2) -> l1 = id1 && l2 = id2) seen then true
  else
    let tm = get_typemap_tm in_gr in
    match (TM.find_opt id1 tm, TM.find_opt id2 tm) with
    | Some ty1, Some ty2 ->
        structurally_equal in_gr ((id1, id2) :: seen) ty1 ty2
    | None, None -> id1 = 0 && id2 = 0 (* null terminator at end of chain *)
    | _ -> false

and lookup_ty ij in_gr =
  let tm = get_typemap_tm in_gr in
  try TM.find ij tm
  with _ ->
    Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);
    print_endline ("When looking up " ^ string_of_int ij);
    raise (Sem_error "Error looking up type")

and lookup_ty_safe ij in_gr =
  let tm = get_typemap_tm in_gr in
  TM.find_opt ij tm

and find_ty_safe_opt in_gr aty =
  let _, tm, _ = get_typemap in_gr in
  match
    TM.to_seq tm |> Seq.find (fun (_, va) -> structurally_equal in_gr [] aty va)
  with
  | Some (id, _) -> Some id
  | None -> None

and find_ty_safe in_gr aty =
  let _, tm, _ = get_typemap in_gr in
  match
    TM.to_seq tm |> Seq.find (fun (_, va) -> structurally_equal in_gr [] aty va)
  with
  | Some (id, _) -> id
  | None ->
      raise
        (Node_not_found
           ("Type not found by find_ty in typemap: " ^ string_of_if1_ty aty))

and find_ty in_gr aty =
  let tm = get_typemap_tm in_gr in
  let lookin_vals =
    try
      TM.fold
        (fun ke va z ->
          if aty = va then raise (Val_is_found ke)
          else if structurally_equal in_gr [] aty va then
            raise (Val_is_found ke)
          else z)
        tm 0
    with Val_is_found ke -> ke
  in
  if lookin_vals = 0 then
    raise
      (Node_not_found
         ((*
           let _ =
            outs_graph
              {
                nmap = nm;
                eset = pe;
                symtab = sm;
                typemap = (id, tm, tmn);
                w = pi;
              }
          in
          *)
          "Type not found byf ind_ty in typemap: " ^ string_of_if1_ty aty))
  else lookin_vals

and add_sisal_typename in_gr namen ty_id =
  if !Debug.level > 0 then begin
    let stack = get_stack_trace 5 in
    type_trace := (ty_id, namen, stack) :: !type_trace
  end;
  let id, tm, tmn = get_typemap in_gr in
  (ty_id, { in_gr with typemap = (id, tm, MM.add namen ty_id tmn) })

and lookup_by_typename in_gr namen =
  let tmn = get_typename_map in_gr in
  try MM.find namen tmn
  with _ -> raise (Node_not_found "not finding a type in typemap")

and lookup_type_opt ty_id in_gr =
  let _, td, _ = get_typemap in_gr in
  TM.find_opt ty_id td

and is_array_type ty_id in_gr =
  match lookup_type_opt ty_id in_gr with
  | Some (Array_ty _) | Some (Array_dv _) -> true
  | _ -> false

and is_unsigned_type ty_id in_gr =
  match lookup_type_opt ty_id in_gr with
  | Some (Basic bc) ->
      (match bc with
       | ULONG | UINT | USHORT | UBYTE | UCHAR
       | ULONG2  | ULONG3  | ULONG4  | ULONG8  | ULONG16
       | UINT2   | UINT3   | UINT4   | UINT8   | UINT16
       | USHORT2 | USHORT3 | USHORT4 | USHORT8 | USHORT16
       | UBYTE2  | UBYTE3  | UBYTE4  | UBYTE8  | UBYTE16
       | UCHAR2  | UCHAR3  | UCHAR4  | UCHAR8  | UCHAR16 -> true
       | _ -> false)
  | _ -> false

and ast_if1_type aty =
  match aty with
  | Byte2 -> BYTE2
  | Half2 -> HALF2
  | Short2 -> SHORT2
  | Int2 -> INT2
  | Float2 -> FLOAT2
  | Double2 -> DOUBLE2
  | Uint2 -> UINT2
  | Ubyte2 -> UBYTE2
  | Ushort2 -> USHORT2
  | Byte3 -> BYTE3
  | Half3 -> HALF3
  | Short3 -> SHORT3
  | Int3 -> INT3
  | Float3 -> FLOAT3
  | Double3 -> DOUBLE3
  | Uint3 -> UINT3
  | Ubyte3 -> UBYTE3
  | Ushort3 -> USHORT3
  | Byte4 -> BYTE4
  | Half4 -> HALF4
  | Short4 -> SHORT4
  | Int4 -> INT4
  | Float4 -> FLOAT4
  | Double4 -> DOUBLE4
  | Uint4 -> UINT4
  | Ubyte4 -> UBYTE4
  | Ushort4 -> USHORT4
  | Byte8 -> BYTE8
  | Half8 -> HALF8
  | Short8 -> SHORT8
  | Int8 -> INT8
  | Float8 -> FLOAT8
  | Double8 -> DOUBLE8
  | Uint8 -> UINT8
  | Ubyte8 -> UBYTE8
  | Ushort8 -> USHORT8
  | Byte16 -> BYTE16
  | Half16 -> HALF16
  | Short16 -> SHORT16
  | Int16 -> INT16
  | Float16 -> FLOAT16
  | Double16 -> DOUBLE16
  | Uint16 -> UINT16
  | Ubyte16 -> UBYTE16
  | Ushort16 -> USHORT16
  | Char2 -> CHAR2
  | Uchar2 -> UCHAR2
  | Char3 -> CHAR3
  | Uchar3 -> UCHAR3
  | Char4 -> CHAR4
  | Uchar4 -> UCHAR4
  | Char8 -> CHAR8
  | Uchar8 -> UCHAR8
  | Char16 -> CHAR16
  | Uchar16 -> UCHAR16
  | Long2 -> LONG2
  | Long3 -> LONG3
  | Long4 -> LONG4
  | Long8 -> LONG8
  | Long16 -> LONG16
  | Ulong2 -> ULONG2
  | Ulong3 -> ULONG3
  | Ulong4 -> ULONG4
  | Ulong8 -> ULONG8
  | Ulong16 -> ULONG16

and ast_mat_if1_type = function
  | Ast.Mat2 -> MAT2
  | Ast.Mat3 -> MAT3
  | Ast.Mat4 -> MAT4

and is_mat_type = function
  | Basic MAT2 | Basic MAT3 | Basic MAT4 -> true
  | _ -> false

(* For a mat type, return the corresponding float-N vec type for its rows/columns *)
and mat_vec_type = function
  | Basic MAT2 -> Basic FLOAT2
  | Basic MAT3 -> Basic FLOAT3
  | Basic MAT4 -> Basic FLOAT4
  | t -> failwith ("mat_vec_type: not a mat type: " ^ string_of_if1_ty t)

and get_typecast_type = function
  | Boolean_prefix -> BOOLEAN
  | Char_prefix -> CHARACTER
  | Double_prefix -> DOUBLE
  | Integer_prefix -> INTEGRAL
  | Real_prefix -> REAL
  | Uint_prefix -> UINT
  | Short_prefix -> SHORT
  | Ushort_prefix -> USHORT
  | Byte_prefix -> BYTE
  | Ubyte_prefix -> UBYTE
  | Half_prefix -> HALF
  | Uchar_prefix -> UCHAR
  | Long_prefix -> LONG
  | Ulong_prefix -> ULONG

and add_sisal_type
    { nmap = nm; eset = pe; symtab = sm; typemap = id, tm, tmn; w = pi } aty =
  let in_gr =
    { nmap = nm; eset = pe; symtab = sm; typemap = (id, tm, tmn); w = pi }
  in
  match aty with
  | Boolean -> (lookup_tyid_triple BOOLEAN, in_gr)
  | Character -> (lookup_tyid_triple CHARACTER, in_gr)
  | Double_real -> (lookup_tyid_triple DOUBLE, in_gr)
  | Integer -> (lookup_tyid_triple INTEGRAL, in_gr)
  | Null -> (lookup_tyid_triple NULL, in_gr)
  | Real -> (lookup_tyid_triple REAL, in_gr)
  | Byte_ty -> (lookup_tyid_triple BYTE, in_gr)
  | Half_ty -> (lookup_tyid_triple HALF, in_gr)
  | Ubyte_ty -> (lookup_tyid_triple UBYTE, in_gr)
  | Uchar_ty -> (lookup_tyid_triple UCHAR, in_gr)
  | Uint_ty -> (lookup_tyid_triple UINT, in_gr)
  | Ushort_ty -> (lookup_tyid_triple USHORT, in_gr)
  | Short_ty -> (lookup_tyid_triple SHORT, in_gr)
  | Long_ty -> (lookup_tyid_triple LONG, in_gr)
  | Ulong_ty -> (lookup_tyid_triple ULONG, in_gr)
  | Vec_ty vx ->
      let g =
        match vx with
        | Byte2 -> BYTE2
        | Half2 -> HALF2
        | Short2 -> SHORT2
        | Int2 -> INT2
        | Float2 -> FLOAT2
        | Double2 -> DOUBLE2
        | Uint2 -> UINT2
        | Ubyte2 -> UBYTE2
        | Ushort2 -> USHORT2
        | Byte3 -> BYTE3
        | Half3 -> HALF3
        | Short3 -> SHORT3
        | Int3 -> INT3
        | Float3 -> FLOAT3
        | Double3 -> DOUBLE3
        | Uint3 -> UINT3
        | Ubyte3 -> UBYTE3
        | Ushort3 -> USHORT3
        | Byte4 -> BYTE4
        | Half4 -> HALF4
        | Short4 -> SHORT4
        | Int4 -> INT4
        | Float4 -> FLOAT4
        | Double4 -> DOUBLE4
        | Uint4 -> UINT4
        | Ubyte4 -> UBYTE4
        | Ushort4 -> USHORT4
        | Byte8 -> BYTE8
        | Half8 -> HALF8
        | Short8 -> SHORT8
        | Int8 -> INT8
        | Float8 -> FLOAT8
        | Double8 -> DOUBLE8
        | Uint8 -> UINT8
        | Ubyte8 -> UBYTE8
        | Ushort8 -> USHORT8
        | Byte16 -> BYTE16
        | Half16 -> HALF16
        | Short16 -> SHORT16
        | Int16 -> INT16
        | Float16 -> FLOAT16
        | Double16 -> DOUBLE16
        | Uint16 -> UINT16
        | Ubyte16 -> UBYTE16
        | Ushort16 -> USHORT16
        | Char2 -> CHAR2
        | Uchar2 -> UCHAR2
        | Char3 -> CHAR3
        | Uchar3 -> UCHAR3
        | Char4 -> CHAR4
        | Uchar4 -> UCHAR4
        | Char8 -> CHAR8
        | Uchar8 -> UCHAR8
        | Char16 -> CHAR16
        | Uchar16 -> UCHAR16
        | Long2 -> LONG2
        | Long3 -> LONG3
        | Long4 -> LONG4
        | Long8 -> LONG8
        | Long16 -> LONG16
        | Ulong2 -> ULONG2
        | Ulong3 -> ULONG3
        | Ulong4 -> ULONG4
        | Ulong8 -> ULONG8
        | Ulong16 -> ULONG16
      in
      (lookup_tyid_triple g, in_gr)
  | Mat_ty x -> (
      match x with
      | Mat2 -> (lookup_tyid_triple MAT2, in_gr)
      | Mat3 -> (lookup_tyid_triple MAT3, in_gr)
      | Mat4 -> (lookup_tyid_triple MAT4, in_gr))
  | Compound_type ct ->
      add_compound_type
        { nmap = nm; eset = pe; symtab = sm; typemap = (id, tm, tmn); w = pi }
        ct
  | Ast.Error_ty st -> add_type_to_typemap (ERROR st) in_gr
  | Ast.Type_name ty -> (
      match MM.mem ty tmn with
      | true -> ((MM.find ty tmn, 0, MM.find ty tmn), in_gr)
      | false ->
          let _ = string_of_graph in_gr in
          raise
            (Printexc.print_raw_backtrace stdout (Printexc.get_callstack 150);
             Node_not_found ("typename being looked up:" ^ ty)))

and add_local_sym in_gr sym_name (sym_def, def_port, def_ty) =
  let cs, ps = get_symtab in_gr in
  let cs =
    SM.add sym_name
      { val_name = sym_name; val_ty = def_ty; val_def = sym_def; def_port }
      cs
  in
  { in_gr with symtab = (cs, ps) }

and get_typemap_tm { nmap = _; eset = _; symtab = _; typemap = _, tm, _; w = _ }
    =
  tm

and get_typename_map in_gr =
  let _, _, tm = in_gr.typemap in
  tm

and get_parent_symtab in_gr = snd in_gr.symtab
and get_local_symtab in_gr = fst in_gr.symtab
and get_but_symtab in_gr = (in_gr.nmap, in_gr.eset, in_gr.typemap, in_gr.w)

and get_a_new_graph in_gr =
  let in_gr = get_symtab_for_new_scope in_gr in
  let ps = get_parent_symtab in_gr in
  let tmmi = get_typemap in_gr in
  let out_gr = get_empty_graph 1 88 in
  let tmn1 = get_typemap out_gr in
  let tmn1 = merge_typeblobs tmn1 tmmi in
  { out_gr with symtab = (SM.empty, ps); typemap = tmn1 }

and num_to_node_sym = function
  | 0 -> BOUNDARY
  | 1 -> CONSTANT
  | 2 -> GRAPH
  | 3 -> OLD
  | 4 -> VAL
  | 5 -> INVOCATION
  | 6 -> NOT
  | 7 -> NEGATE
  | 8 -> ACATENATE
  | 9 -> AND
  | 10 -> IDIVIDE
  | 11 -> TIMES
  | 12 -> SUBTRACT
  | 13 -> ADD
  | 14 -> OR
  | 15 -> NOT_EQUAL
  | 16 -> EQUAL
  | 17 -> LESSER_EQUAL
  | 18 -> LESSER
  | 19 -> GREATER_EQUAL
  | 20 -> GREATER
  | 21 -> RBUILD
  | 22 -> RELEMENTS
  | 23 -> RREPLACE
  | 24 -> SBUILD
  | 25 -> SAPPEND
  | 26 -> TAGCASE
  | 27 -> SELECT
  | 28 -> RANGEGEN
  | 29 -> AADDH
  | 30 -> AADDL
  | 31 -> ABUILD
  | 32 -> AELEMENT
  | 33 -> AFILL
  | 34 -> AGATHER
  | 35 -> AISEMPTY
  | 36 -> ALIML
  | 37 -> ALIMH
  | 38 -> AREPLACE
  | 39 -> AREML
  | 40 -> AREMH
  | 41 -> ASCATTER
  | 42 -> ASETL
  | 43 -> ASIZE
  | 44 -> INTERNAL
  | 45 -> REDUCE
  | 46 -> REDUCELEFT
  | 47 -> REDUCERIGHT
  | 48 -> REDUCETREE
  | 49 -> STREAM
  | 50 -> FINALVALUE
  | 51 -> MULTIARITY
  | 52 -> SWIZZLE
  | 53 -> VEC
  | 54 -> MAT
  | 55 -> VSPLAT
  | 56 -> VBUILD
  | 57 -> MATSPLAT
  | 58 -> MATBUILD
  | 59 -> TYPECAST
  | 60 -> ACREATE
  | 61 -> FDIVIDE
  | 62 -> ERROR_NODE
  | 63 -> AADJUST
  | 64 -> STRM_FIRST
  | 65 -> STRM_REST
  | 66 -> BITAND
  | 67 -> BITOR
  | 68 -> BITXOR
  | 69 -> STRM_APPEND
  | 70 -> STRM_EMPTY
  | 71 -> MATMUL
  | 72 -> MATVECMUL
  | 73 -> VECMATMUL
  | 74 -> DOT
  | 75 -> SHL
  | 76 -> SHR
  | 77 -> ASHR
  | _ -> raise (Sem_error "Error looking up type")

and node_sym_to_num = function
  | AADDH -> 29
  | AADDL -> 30
  | ABUILD -> 31
  | ACATENATE -> 8
  | ACREATE -> 60
  | ADD -> 13
  | AELEMENT -> 32
  | AFILL -> 33
  | AGATHER -> 34
  | AISEMPTY -> 35
  | ALIMH -> 37
  | ALIML -> 36
  | AND -> 9
  | AREMH -> 40
  | AREML -> 39
  | AREPLACE -> 38
  | ASCATTER -> 41
  | ASETL -> 42
  | ASIZE -> 43
  | BOUNDARY -> 0
  | CONSTANT -> 1
  | EQUAL -> 16
  | FDIVIDE -> 61
  | FINALVALUE -> 50
  | GRAPH -> 2
  | GREATER -> 20
  | GREATER_EQUAL -> 19
  | IDIVIDE -> 10
  | INTERNAL -> 44
  | INVOCATION -> 5
  | LESSER -> 18
  | LESSER_EQUAL -> 17
  | MAT -> 53
  | MATBUILD -> 58
  | MATSPLAT -> 57
  | MATMUL -> 71
  | MATVECMUL -> 72
  | VECMATMUL -> 73
  | DOT -> 74
  | MULTIARITY -> 51
  | NEGATE -> 7
  | NOT -> 6
  | NOT_EQUAL -> 15
  | OLD -> 3
  | OR -> 14
  | RANGEGEN -> 28
  | RBUILD -> 21
  | REDUCE -> 45
  | REDUCELEFT -> 46
  | REDUCERIGHT -> 47
  | REDUCETREE -> 48
  | RELEMENTS -> 22
  | RREPLACE -> 23
  | SAPPEND -> 25
  | SBUILD -> 24
  | SELECT -> 27
  | STREAM -> 49
  | SUBTRACT -> 12
  | SWIZZLE -> 52
  | TAGCASE -> 26
  | TIMES -> 11
  | TYPECAST -> 59
  | VAL -> 4
  | VEC -> 54
  | VBUILD -> 56
  | VSPLAT -> 55
  | ERROR_NODE -> 62
  | AADJUST -> 63
  | STRM_FIRST -> 64
  | STRM_REST -> 65
  | BITAND -> 66
  | BITXOR -> 67
  | BITOR -> 68
  | STRM_APPEND -> 69
  | STRM_EMPTY -> 70
  | SHL -> 75
  | SHR -> 76
  | ASHR -> 77
  | DV_CREATE -> 78
  | DV_ELEMENT -> 79
  | DV_REPLACE -> 80
  | DV_GATHER -> 81
  | DV_SCATTER -> 125
  | DV_RESHAPE -> 82
  | DV_SLICE -> 83
  | DV_PERMUTE -> 84
  | DV_ROTATE -> 85
  | DV_COMPRESS -> 86
  | DV_OUTERPRODUCT -> 87
  | DV_GRADE_UP -> 88
  | DV_GRADE_DOWN -> 89
  | DV_SORT -> 90
  | DV_REVERSE -> 91
  | MAP_NODE -> 92
  | FOLDL_NODE -> 93
  | FOLDR_NODE -> 94
  | SCAN_NODE -> 95
  | REDUCE_ALL -> 96
  | BROADCAST_SCALAR -> 97
  | ARGMAX_NODE -> 98
  | ARGMIN_NODE -> 99
  | NONZERO_NODE -> 100
  | WHERE_NODE -> 101
  | REDUCE_AXIS -> 102
  | MEAN_NODE -> 103
  | VARIANCE_NODE -> 104
  | STDDEV_NODE -> 105
  | ANY_NODE -> 106
  | ALL_NODE -> 107
  | NORM_NODE -> 108
  | CUMSUM_NODE -> 109
  | CUMPROD_NODE -> 110
  | CONCAT_NODE -> 111
  | TILE_NODE -> 112
  | SQUEEZE_NODE -> 113
  | EXPAND_NODE -> 114
  | RAVEL_NODE -> 115
  | STENCIL_NODE -> 116
  | PAD_NODE -> 117
  | INNERPRODUCT_NODE -> 118
  | EINSUM_NODE -> 127
  | GET_DOPE_VEC -> 119
  | SHAPE_CHECK  -> 120
  | DV_CONFORM   -> 121
  | DV_NUM_RANK  -> 122
  | DV_DIMENSION -> 123
  | DV_OFFSET_AT -> 124
  | DV_LOAD_LINEAR -> 125
  | DV_RESHAPE_BY_SHAPE -> 126
  | CONV_H -> 127
  | CONV_V -> 128
  | CONV_2D -> 129

and string_of_node_sym = function
  | AADDH -> "ARRAY_ADDH"
  | AADDL -> "ARRAY_ADDL"
  | ABUILD -> "ARRAY_BUILD"
  | ACATENATE -> "ARRAY_CATENATE"
  | ACREATE -> "ARRAY_CREATE"
  | ADD -> "ADD"
  | AELEMENT -> "ARRAY_ELEMENT"
  | AFILL -> "ARRAY_FILL"
  | AGATHER -> "ARRAY_GATHER"
  | AISEMPTY -> "AISEMPTY"
  | ALIMH -> "ARRAY_LIMH"
  | ALIML -> "ARRAY_LIML"
  | AADJUST -> "ARRAY_ADJUST"
  | AND -> "AND"
  | AREMH -> "ARRAY_REMH"
  | AREML -> "ARRAY_REML"
  | AREPLACE -> "ARRAY_REPLACE"
  | ASCATTER -> "ARRAY_SCATTER"
  | ASETL -> "ARRAY_SETL"
  | ASIZE -> "ARRAY_SIZE"
  | BITAND -> "BITWISE_AND"
  | BITOR -> "BITWISE_OR"
  | BITXOR -> "BITWISE_XOR"
  | SHL -> "SHL"
  | SHR -> "SHR"
  | ASHR -> "ASHR"
  | BOUNDARY -> "BOUNDARY"
  | CONSTANT -> "CONSTANT"
  | EQUAL -> "EQUAL"
  | FDIVIDE -> "FDIVIDE"
  | FINALVALUE -> "FINALVALUE"
  | GRAPH -> "GRAPH"
  | GREATER -> "GREATER"
  | GREATER_EQUAL -> "GREATER_EQUAL"
  | IDIVIDE -> "IDIVIDE"
  | INTERNAL -> ""
  | INVOCATION -> "INVOCATION"
  | LESSER -> "LESSER"
  | LESSER_EQUAL -> "LESSER_EQUAL"
  | MAT -> "MAT"
  | MATBUILD -> "MATBUILD"
  | MATSPLAT -> "MATSPLAT"
  | MATMUL -> "MATMUL"
  | MATVECMUL -> "MATVECMUL"
  | VECMATMUL -> "VECMATMUL"
  | DOT -> "DOT"
  | MULTIARITY -> "MULTIARITY"
  | NEGATE -> "NEGATE"
  | NOT -> "NOT"
  | NOT_EQUAL -> "NOT_EQUAL"
  | OLD -> "OLD"
  | OR -> "OR"
  | RANGEGEN -> "RANGEGEN"
  | RBUILD -> "RBUILD"
  | REDUCE -> "REDUCE"
  | REDUCELEFT -> "REDUCELEFT"
  | REDUCERIGHT -> "REDUCERIGHT"
  | REDUCETREE -> "REDUCETREE"
  | RELEMENTS -> "RELEMENTS"
  | RREPLACE -> "RREPLACE"
  | SAPPEND -> "SAPPEND"
  | SBUILD -> "SBUILD"
  | SELECT -> "SELECT"
  | STREAM -> "STREAM"
  | SUBTRACT -> "SUBTRACT"
  | SWIZZLE -> "SWIZZLE"
  | TAGCASE -> "TAGCASE"
  | TIMES -> "TIMES"
  | TYPECAST -> "TYPECAST"
  | VAL -> "VAL"
  | VEC -> "VEC"
  | VBUILD -> "VBUILD"
  | VSPLAT -> "VSPLAT"
  | ERROR_NODE -> "ERROR"
  | STRM_APPEND -> "STREAM_APPEND"
  | STRM_EMPTY -> "STREAM_EMPTY"
  | STRM_FIRST -> "STREAM_FIRST"
  | STRM_REST -> "STREAM_REST"
  | DV_CREATE -> "DV_CREATE"
  | DV_ELEMENT -> "DV_ELEMENT"
  | DV_REPLACE -> "DV_REPLACE"
  | DV_GATHER -> "DV_GATHER"
  | DV_SCATTER -> "DV_SCATTER"
  | DV_RESHAPE -> "DV_RESHAPE"
  | DV_SLICE -> "DV_SLICE"
  | DV_PERMUTE -> "DV_PERMUTE"
  | DV_ROTATE -> "DV_ROTATE"
  | DV_COMPRESS -> "DV_COMPRESS"
  | DV_OUTERPRODUCT -> "DV_OUTERPRODUCT"
  | DV_GRADE_UP -> "DV_GRADE_UP"
  | DV_GRADE_DOWN -> "DV_GRADE_DOWN"
  | DV_SORT -> "DV_SORT"
  | DV_REVERSE -> "DV_REVERSE"
  | MAP_NODE -> "MAP"
  | REDUCE_ALL -> "REDUCE_ALL"
  | FOLDL_NODE -> "FOLDL_NODE"
  | FOLDR_NODE -> "FOLDR_NODE"
  | SCAN_NODE -> "SCAN_NODE"
  | BROADCAST_SCALAR -> "BROADCAST_SCALAR"
  | ARGMAX_NODE -> "ARGMAX"
  | ARGMIN_NODE -> "ARGMIN"
  | NONZERO_NODE -> "NONZERO"
  | WHERE_NODE -> "WHERE"
  | REDUCE_AXIS -> "REDUCE_AXIS"
  | MEAN_NODE -> "MEAN"
  | VARIANCE_NODE -> "VARIANCE"
  | STDDEV_NODE -> "STDDEV"
  | ANY_NODE -> "ANY"
  | ALL_NODE -> "ALL"
  | NORM_NODE -> "NORM"
  | CUMSUM_NODE -> "CUMSUM"
  | CUMPROD_NODE -> "CUMPROD"
  | CONCAT_NODE -> "CONCAT"
  | TILE_NODE -> "TILE"
  | SQUEEZE_NODE -> "SQUEEZE"
  | EXPAND_NODE -> "EXPAND"
  | RAVEL_NODE -> "RAVEL"
  | STENCIL_NODE -> "STENCIL"
  | PAD_NODE -> "PAD"
  | INNERPRODUCT_NODE -> "INNERPRODUCT"
  | EINSUM_NODE -> "EINSUM"
  | GET_DOPE_VEC -> "GET_DOPE_VEC"
  | SHAPE_CHECK  -> "SHAPE_CHECK"
  | DV_CONFORM   -> "DV_CONFORM"
  | DV_NUM_RANK  -> "DV_NUM_RANK"
  | DV_DIMENSION   -> "DV_DIMENSION"
  | DV_OFFSET_AT   -> "DV_OFFSET_AT"
  | DV_LOAD_LINEAR -> "DV_LOAD_LINEAR"
  | DV_RESHAPE_BY_SHAPE -> "DV_RESHAPE_BY_SHAPE"
  | CONV_H -> "CONV_H"
  | CONV_V -> "CONV_V"
  | CONV_2D -> "CONV_2D"

  and string_of_pragmas p =
  List.fold_right
    (fun p q ->
      let l =
        match p with
        | Bounds (i, j) ->
            "Bounds (" ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
        | SrcLine (i, j) ->
            "SrcLine (" ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
        | OpNum i -> "OpNum " ^ string_of_int i
        | Ar i -> "Ar " ^ string_of_int i
        | Of i -> "Of " ^ string_of_int i
        | Lazy -> "Lazy"
        | Name str -> "%na=" ^ str
        | Ref -> "Ref"
        | Pointer -> "Pointer"
        | Contiguous -> "Contiguous"
        | No_pragma -> ""
        | Ast_type _ -> ""
        | Subscript s -> "Subscript(" ^ s ^ ")"
      in
      cate_nicer l q " ,")
    p ""

and quick_lookup_native_type a =
  if a < 88 then rev_lookup_ty_name a else string_of_int a

and string_of_if1_ty ity =
  match ity with
  | Typed_error a -> "ERROR " ^ quick_lookup_native_type a
  | Array_ty a -> "ARRAY " ^ quick_lookup_native_type a
  | Array_dv a ->
      "ARRAY_DV " ^ quick_lookup_native_type a
  | Basic bc -> string_of_if1_basic_ty bc
  | Function_ty (if1l, if2l, fn_name) ->
      "FUNCTION_TYPE " ^ fn_name ^ " (ARGS: " ^ string_of_int if1l
      ^ ") (RETURNS:" ^ string_of_int if2l ^ ")"
  | Multiple bc -> "Multiple " ^ string_of_if1_basic_ty bc
  | Record (fty, nfty, namen) ->
      "RECORD {"
      ^ cate_list
          [
            "Type label:" ^ quick_lookup_native_type fty;
            "Next field:" ^ quick_lookup_native_type nfty;
            "%na=" ^ namen;
          ]
          "; "
      ^ "}"
  | Stream bc -> "STREAM (" ^ string_of_int bc ^ ")"
  | Tuple_ty (fty, nty) ->
      "TUPLE {"
      ^ cate_list
          [
            "Type label:" ^ quick_lookup_native_type fty;
            "Next label:" ^ quick_lookup_native_type nty;
          ]
          "; "
      ^ "}"
  | Union (lab1, lab2, namen) ->
      "UNION {"
      ^ cate_list
          [
            "Type label:" ^ quick_lookup_native_type lab1;
            "Next tag:" ^ string_of_int lab2;
            "%na=" ^ namen;
          ]
          "; "
      ^ "}"
  | Unknown_ty -> ""
  | Field if1li ->
      "Fields "
      ^ List.fold_right (fun x y -> string_of_int x ^ "; " ^ y) if1li ""
  | Tag if1li ->
      "Tags " ^ List.fold_right (fun x y -> string_of_int x ^ "; " ^ y) if1li ""
  | If1Type_name tt -> "TYPENAME " ^ string_of_int tt
  | ERROR e -> "PANIC[" ^ e ^ "]"

and string_of_if1_basic_ty bc =
  match bc with
  | ARRAY -> "ARRAY"
  | BOOLEAN -> "BOOLEAN"
  | BYTE -> "BYTE"
  | BYTE16 -> "BYTE16"
  | BYTE2 -> "BYTE2"
  | BYTE3 -> "BYTE3"
  | BYTE4 -> "BYTE4"
  | BYTE8 -> "BYTE8"
  | CHAR16 -> "CHAR16"
  | CHAR2 -> "CHAR2"
  | CHAR3 -> "CHAR3"
  | CHAR4 -> "CHAR4"
  | CHAR8 -> "CHAR8"
  | CHARACTER -> "CHARACTER"
  | DOUBLE -> "DOUBLE"
  | DOUBLE16 -> "DOUBLE16"
  | DOUBLE2 -> "DOUBLE2"
  | DOUBLE3 -> "DOUBLE3"
  | DOUBLE4 -> "DOUBLE4"
  | DOUBLE8 -> "DOUBLE8"
  | FLOAT16 -> "FLOAT16"
  | FLOAT2 -> "FLOAT2"
  | FLOAT3 -> "FLOAT3"
  | FLOAT4 -> "FLOAT4"
  | FLOAT8 -> "FLOAT8"
  | HALF -> "HALF"
  | HALF16 -> "HALF16"
  | HALF2 -> "HALF2"
  | HALF3 -> "HALF3"
  | HALF4 -> "HALF4"
  | HALF8 -> "HALF8"
  | INT16 -> "INT16"
  | INT2 -> "INT2"
  | INT3 -> "INT3"
  | INT4 -> "INT4"
  | INT8 -> "INT8"
  | INTEGRAL -> "INTEGRAL"
  | LONG -> "LONG"
  | LONG16 -> "LONG16"
  | LONG2 -> "LONG2"
  | LONG3 -> "LONG3"
  | LONG4 -> "LONG4"
  | LONG8 -> "LONG8"
  | MAT2 -> "MAT2"
  | MAT3 -> "MAT3"
  | MAT4 -> "MAT4"
  | NULL -> "NULL"
  | REAL -> "REAL"
  | RECORD -> "RECORD"
  | SHORT -> "SHORT"
  | SHORT16 -> "SHORT16"
  | SHORT2 -> "SHORT2"
  | SHORT3 -> "SHORT3"
  | SHORT4 -> "SHORT4"
  | SHORT8 -> "SHORT8"
  | STREAM -> "STREAM"
  | UBYTE -> "UBYTE"
  | UBYTE16 -> "UBYTE16"
  | UBYTE2 -> "UBYTE2"
  | UBYTE3 -> "UBYTE3"
  | UBYTE4 -> "UBYTE4"
  | UBYTE8 -> "UBYTE8"
  | UCHAR -> "UCHAR"
  | UCHAR16 -> "UCHAR16"
  | UCHAR2 -> "UCHAR2"
  | UCHAR3 -> "UCHAR3"
  | UCHAR4 -> "UCHAR4"
  | UCHAR8 -> "UCHAR8"
  | UINT -> "UINT"
  | UINT16 -> "UINT16"
  | UINT2 -> "UINT2"
  | UINT3 -> "UINT3"
  | UINT4 -> "UINT4"
  | UINT8 -> "UINT8"
  | ULONG -> "ULONG"
  | ULONG16 -> "ULONG16"
  | ULONG2 -> "ULONG2"
  | ULONG3 -> "ULONG3"
  | ULONG4 -> "ULONG4"
  | ULONG8 -> "ULONG8"
  | UNION -> "UNION"
  | USHORT -> "USHORT"
  | USHORT16 -> "USHORT16"
  | USHORT2 -> "USHORT2"
  | USHORT3 -> "USHORT3"
  | USHORT4 -> "USHORT4"
  | USHORT8 -> "USHORT8"

and is_basic_int_scalar bc =
  match bc with INTEGRAL | LONG -> true | _ -> false

and graph_clean_multiarity in_gr = cleanup_multiarity in_gr

and string_of_ports pa =
  "[|" ^ Array.fold_right (fun x y -> cate_nicer x y ",") pa "" ^ "|]"

and string_of_pair_list zz =
  "["
  ^ List.fold_right
      (fun (x, y) z ->
        cate_nicer (("(" ^ string_of_int x) ^ "," ^ string_of_int y ^ ")") z ";")
      zz ""
  ^ "]"

and string_of_pair_list_final_string zz =
  "["
  ^ List.fold_right
      (fun (x, y, w) z ->
        cate_nicer
          (("(" ^ string_of_int x) ^ "," ^ string_of_int y ^ "," ^ w ^ ")")
          z ";")
      zz ""
  ^ "]"

and string_of_node_ty ?(offset = 2) in_gr n =
  match n with
  | Literal (lab, _, str, _) ->
      string_of_int lab (*^ " " ^ (string_of_if1_basic_ty ty)*)
      ^ " \"" ^ str ^ "\"" (*^ (string_of_ports pout)*)
  | Simple (lab, n, pin, pout, prag) ->
      cate_nicer
        (cate_nicer
           (cate_nicer
              (cate_nicer (string_of_int lab) (string_of_node_sym n) " ")
              (string_of_ports pin) " ")
           (string_of_ports pout) " ")
        (string_of_pragmas prag) " "
  | Compound (lab, sy, ty, pl, g, assoc) ->
      cate_nicer
        (cate_nicer
           (cate_nicer
              (cate_nicer
                 (string_of_int lab ^ " " ^ string_of_int ty)
                 (string_of_pragmas pl) " ")
              (string_of_graph ~offset:(offset + 2) g)
              "\n")
           (string_of_node_sym sy) " ")
        (List.fold_right
           (fun x y -> cate_nicer (string_of_int x) y ",")
           assoc "")
        " "
  | Unknown_node -> "Unknown"
  | Boundary (zz, yy, errs, pp) ->
      let str_errs =
        List.fold_left
          (fun acc (lab, ty_id) ->
            let _, tm, _ = in_gr.typemap in
            let desc =
              match TM.find_opt ty_id tm with
              | Some (ERROR s) -> "PANIC:" ^ s
              | _ -> "TY:" ^ string_of_int ty_id
            in
            acc ^ Printf.sprintf "(%s,%d)" desc lab)
          "" errs
      in
      let bb =
        cate_nicer
          (cate_nicer
             (cate_nicer
                (string_of_pair_list_final_string zz)
                (string_of_pair_list yy) ", ")
             (string_of_pragmas pp) ", ")
          str_errs ", "
      in
      "BOUNDARY [" ^ bb ^ "]"

and string_of_node n_int g = string_of_node_ty g (get_node n_int g)

and string_of_edge in_gr ((n1, p1), (n2, p2), tt) =
  let _, tm, _ = in_gr.typemap in

  (* 1. Lookup the type definition to see if it's a "Panic" signal *)
  let is_error, type_desc =
    match TM.find_opt tt tm with
    | Some (ERROR s) -> (true, "ERR:" ^ s)
    | Some _ -> (false, printable_full_type (get_typemap_tm in_gr) tt)
    | None -> (false, "U_NKNOWN")
  in

  (* 2. Use double-colon '::' for Railroad edges, single ':' for Math edges *)
  let sep1 = if is_error then "::" else ":" in
  let sep2 = if is_error then "::" else ":" in

  (* 3. Compose the final "Nicer" string *)
  let connection = Printf.sprintf "%d%s%d -> %d%s%d" n1 sep1 p1 n2 sep2 p2 in
  let metadata = Printf.sprintf "[ID:%d %s]" tt type_desc in

  cate_nicer connection metadata " "

and string_of_edge_set in_gr ne =
  let ee = ES.fold (fun x y -> string_of_edge in_gr x :: y) ne [] in
  match ee with [] -> [] | _ -> "----EDGES----" :: ee

and string_of_node_map ?(offset = 2) in_gr =
  let mn = in_gr.nmap in
  let nn =
    NM.fold (fun _ v z -> string_of_node_ty in_gr ~offset v :: z) mn []
  in
  match nn with [] -> [] | _ -> "----NODES----" :: nn

and string_of_if1_value tm = function
  | { val_ty = ii; val_name = st; val_def = jj; def_port = p } ->
      let ttt =
        match TM.mem ii tm with
        | true -> printable_full_type tm ii
        | false -> ""
      in
      ttt ^ "; " ^ st ^ "; " ^ "(" ^ string_of_int jj ^ " : " ^ string_of_int p
      ^ ")"

and string_of_if1_value_in tm = function
  | { val_ty = ii; val_name = st; val_def = jj; def_port = p } ->
      let ttt =
        match TM.mem ii tm with
        | true ->
            string_of_if1_ty
              (match TM.find_opt ii tm with
              | Some x -> x
              | None -> failwith "Error in string_of_if1_value_in")
        | false -> ""
      in
      if jj = 0 then
        ttt ^ ";" ^ st ^ ";" ^ "(" ^ string_of_int jj ^ "," ^ string_of_int p
        ^ ")"
      else ""

and string_of_if1_value_out tm = function
  | { val_ty = ii; val_name = st; val_def = jj; def_port = p } ->
      let ttt =
        match TM.mem ii tm with
        | true ->
            string_of_if1_ty
              (match TM.find_opt ii tm with
              | Some x -> x
              | None -> failwith "Error in string_of_if1_value_in")
        | false -> ""
      in
      if jj <> 0 then
        "{" ^ ttt ^ ";" ^ st ^ ";" ^ "(" ^ string_of_int jj ^ ","
        ^ string_of_int p ^ ")}"
      else ""

and string_of_symtab_gr in_gr =
  let { nmap = _; eset = _; symtab = ls, _; typemap = _, tm, _; w = _ } =
    in_gr
  in
  SM.fold (fun _ v z -> string_of_if1_value tm v :: z) ls []

and string_of_symtab_gr_in in_gr =
  let { nmap = _; eset = _; symtab = ls, _; typemap = _, tm, _; w = _ } =
    in_gr
  in
  SM.fold (fun _ v z -> string_of_if1_value_in tm v :: z) ls []

and string_of_symtab_gr_out in_gr =
  let { nmap = _; eset = _; symtab = ls, _; typemap = _, tm, _; w = _ } =
    in_gr
  in
  SM.fold (fun _ v z -> string_of_if1_value_out tm v :: z) ls []

and string_of_symtab (ls, gs) tm =
  let ls = SM.fold (fun _ v z -> string_of_if1_value tm v :: z) ls [] in
  let ls = match ls with [] -> [] | _ -> "LOCAL-SYM: " :: ls in
  let gs = SM.fold (fun _ v z -> string_of_if1_value tm v :: z) gs [] in
  let gs = match gs with [] -> [] | _ -> "GLOBAL-SYM: " :: gs in
  gs @ ls

and typenames_to_string typemap =
  Format.asprintf "@[<v 0>@[<hov 0>%a@]@]"
    (fun ppf map ->
      let margin = 80 in
      let reserved_threshold = 83 in
      (* Adjust this to your specific reserved count *)
      Format.pp_set_margin ppf margin;
      MM.iter
        (fun name type_num ->
          if type_num > reserved_threshold then
            (* Use @  to hint at a break point for the 80-char limit *)
            Format.fprintf ppf "  [%s:%d]@ " name type_num
          else ())
        map)
    typemap

and string_of_typenames tmn =
  if tmn == MM.empty then []
  else "-----TYPENAMES----" :: [ typenames_to_string tmn ]

and print_typemap typemap =
  let open Format in
  (* Set the margin to 80 characters *)
  set_margin 80;

  printf "@[<v 0>--- TYPEMAP ---@,";
  printf "@[<hov 2>";

  (* hov box: breaks lines if they don't fit *)
  TM.iter
    (fun id v ->
      let type_str = string_of_if1_ty v in
      let entry = sprintf "[%d:%s]" id type_str in

      (* @  is a "hint" to the formatter: "You can break here if needed" *)
      printf "%s@ " entry)
    typemap;

  printf "@]@,--- END TYPEMAP ---@]@."

and typemap_to_string typemap =
  Format.asprintf "@[<v 0>@[<hov 0>%a@]@]"
    (fun ppf map ->
      let margin = 80 in
      let reserved_threshold = 83 in
      (* Adjust this to your specific reserved count *)
      Format.pp_set_margin ppf margin;
      TM.iter
        (fun id v ->
          (* Only print types created by the program/lowering, skipping standard primitives *)
          if id >= reserved_threshold then
            let type_str = string_of_if1_ty v in
            Format.fprintf ppf "  [%d:%s]@ " id type_str)
        map)
    typemap

and string_of_graph ?(offset = 0) in_gr =
  let { nmap = _; eset = ne; symtab = sm; typemap = _, tm, tmn; w = tail } =
    in_gr
  in
  cate_list_pad offset
    (("Graph {" :: string_of_node_map ~offset in_gr)
    @ string_of_edge_set in_gr ne
    @ string_of_symtab sm tm
    @ ([ typemap_to_string tm ] @ string_of_typenames tmn)
    @ [ "} " ^ string_of_int tail ])
    "\n"

and string_of_typemap tm =
  let tm =
    TM.fold
      (fun k v z -> (string_of_int k ^ " " ^ string_of_if1_ty v) :: z)
      tm []
  in
  match tm with [] -> [] | _ -> "----TYPEMAP----" :: tm

and string_of_tyblob (x, y, z) =
  cate_list_pad 0
    ((("ty_num:" ^ string_of_int x) :: string_of_typemap y)
    @ string_of_typenames z)
    "\n"

and string_of_triple_int (i, j, k) =
  "(" ^ string_of_int i ^ ", " ^ string_of_int j ^ ", " ^ string_of_int k ^ ")"

and string_of_triple_int_list zz =
  List.fold_left (fun zz (i, j, k) -> zz ^ string_of_triple_int (i, j, k)) "" zz

and string_of_graph_thin ?(offset = 0) in_gr =
  cate_list_pad offset
    (("Graph {" :: string_of_node_map ~offset in_gr)
    @ string_of_edge_set in_gr in_gr.eset
    @ [ "} " ^ string_of_int in_gr.w ])
    "\n"

and string_of_graph2 (_, gr) = string_of_graph gr

and graph_printer fmt gr =
  Format.fprintf fmt "-------\n%s\n" (string_of_graph ~offset:2 gr)

and int_map_printer fmt inmap =
  Format.fprintf fmt "-------\n%s\n"
    ((IntMap.fold (fun ke valu old ->
          string_of_int ke ^ " : " ^ string_of_int valu ^ "\n" ^ old))
       inmap "")

and outs_graph gr =
  Printexc.print_raw_backtrace stdout (Printexc.get_callstack 5);
  graph_printer Format.std_formatter gr

and outs_graph_with_msg msg gr =
  print_endline msg;
  outs_graph gr

and node_printer fmt ii in_gr =
  Format.fprintf fmt "------\n%s\n" (string_of_node ii in_gr)

and outs_node ii gr = node_printer Format.std_formatter ii gr

and nmap_printer fmt in_gr =
  Format.fprintf fmt "------\n%s\n" (cate_list (string_of_node_map in_gr) "\n")

and outs_nmap in_gr = nmap_printer Format.std_formatter in_gr

and symtab_printer fmt (cs, ps, tm) =
  Format.fprintf fmt "----------\n%s\n"
    (cate_list (string_of_symtab (cs, ps) tm) "\n")

and outs_syms { nmap = _; eset = _; symtab = cs, ps; typemap = _, tm, _; w = _ }
    =
  symtab_printer Format.std_formatter (cs, ps, tm)

and string_of_triples_list in_gr triplets =
  let _, tm, _ = in_gr.typemap in
  let string_of_triple (n_idx, p_idx, t_idx) =
    (* 1. Resolve Node Name (Opcode) *)
    let node_name =
      try
        let node_data =
          match NM.find n_idx in_gr.nmap with
          | Simple (_, sym, _, _, _) -> string_of_node_sym sym
          | Literal (_, _, val_str, _) -> "LITERAL(" ^ val_str ^ ")"
          | Compound (_, sym, _, _, _, _) ->
              "COMPOUND(" ^ string_of_node_sym sym ^ ")"
          | Boundary _ -> "BOUNDARY"
          | Unknown_node -> "UNKNOWN"
        in
        node_data
      with _ -> "NODE_NOT_FOUND(" ^ string_of_int n_idx ^ ")"
    in

    (* 2. Resolve Type Name from Typemap *)
    let type_name =
      try
        let ty_struct = TM.find t_idx tm in
        string_of_if1_ty ty_struct
      with _ -> "TYPE_NOT_FOUND(" ^ string_of_int t_idx ^ ")"
    in

    (* 3. Format the triple string *)
    Printf.sprintf "[Node: %s (#%d) | Port: %d | Type: %s (#%d)]" node_name
      n_idx p_idx type_name t_idx
  in

  (* Join all triples into a single block of text *)
  String.concat "\n    " (List.map string_of_triple triplets)

and bind_name nam (n, p, ty) in_gr =
  let cs, ps = get_symtab in_gr in
  {
    in_gr with
    symtab =
      ( SM.add nam { val_ty = ty; val_name = nam; val_def = n; def_port = p } cs,
        ps );
  }

and get_symbol_id v in_gr =
  let cs, ps = get_symtab in_gr in
  (* 1. Check current scope *)
  if SM.mem v cs then
    let entry = SM.find v cs in
    ((entry.val_def, entry.def_port, entry.val_ty), in_gr)
    (* 2. Check parent scope for automatic boundary import *)
  else if SM.mem v ps then
    let p_entry = SM.find v ps in
    (* Physically add the port to the IF1 boundary metadata *)
    let next_port, in_gr =
      add_to_boundary_inputs ~namen:v p_entry.val_def p_entry.def_port in_gr
    in
    (* Define the symbol in current scope as an input from the boundary (Node 0) *)
    let cs =
      SM.add v
        {
          val_ty = p_entry.val_ty;
          val_name = p_entry.val_name;
          val_def = 0;
          def_port = next_port;
        }
        cs
    in
    let in_gr = { in_gr with symtab = (cs, ps) } in
    ((0, next_port, p_entry.val_ty), in_gr)
  else
    raise
      (Sem_error
         ("Undefined name '" ^ v
          ^ "': not in scope. In a 'let' block, names can only reference \
             bindings defined earlier - forward references are not allowed."))

and get_symbol_id_old v in_gr =
  let cs, ps = get_symtab in_gr in
  let old_name = "OLD " ^ v in

  (* 1. Check current scope for an existing "OLD" entry *)
  if SM.mem old_name cs then
    let entry = SM.find old_name cs in
    ((entry.val_def, entry.def_port, entry.val_ty), in_gr)
    (* 2. Check current scope for "v" and create "OLD" alias *)
  else if SM.mem v cs then
    let entry = SM.find v cs in
    let cs = SM.add old_name { entry with val_name = old_name } cs in
    ( (entry.val_def, entry.def_port, entry.val_ty),
      { in_gr with symtab = (cs, ps) } )
    (* 3. Check parent scope for "OLD v" and import through boundary *)
  else if SM.mem old_name ps then
    let p_entry = SM.find old_name ps in
    let next_port, in_gr =
      add_to_boundary_inputs ~namen:old_name p_entry.val_def p_entry.def_port
        in_gr
    in
    let cs =
      SM.add old_name { p_entry with val_def = 0; def_port = next_port } cs
    in
    let in_gr = { in_gr with symtab = (cs, ps) } in
    ((0, next_port, p_entry.val_ty), in_gr)
    (* 4. Check parent scope for "v" and import as "OLD" through boundary *)
  else if SM.mem v ps then
    let p_entry = SM.find v ps in
    let next_port, in_gr =
      add_to_boundary_inputs ~namen:old_name p_entry.val_def p_entry.def_port
        in_gr
    in
    let cs =
      SM.add old_name
        { p_entry with val_name = old_name; val_def = 0; def_port = next_port }
        cs
    in
    let in_gr = { in_gr with symtab = (cs, ps) } in
    ((0, next_port, p_entry.val_ty), in_gr)
  else
    raise
      (Node_not_found
         ("Symbol not found in current or parent symtab: " ^ old_name))

and is_outer_var vv = function
  | { nmap = _; eset = _; symtab = _, ps; typemap = _; w = _ } -> SM.mem vv ps

and dot_of_node_map id mn in_gr =
  NM.fold (fun _ v z -> cate_nicer z (dot_of_node_ty id in_gr v) ";\n") mn ""

and dot_of_edge id ((n1, p1), (n2, p2), tt) =
  let process_n1 id = function
    | 0 -> "IN0" ^ string_of_int id
    | n1 -> string_of_int id ^ string_of_int n1
  in
  let process_n2 id = function
    | 0 -> "OUT0" ^ string_of_int id
    | n2 -> string_of_int id ^ string_of_int n2
  in
  process_n1 id n1 ^ " ->  " ^ process_n2 id n2 ^ " [label=\"("
  ^ string_of_int p1 ^ "," ^ string_of_int p2 ^ "),Ty=" ^ string_of_int tt
  ^ "\"]"

and dot_of_edge_set id ne =
  ES.fold (fun x y -> cate_nicer y (dot_of_edge id x) "\n") ne ""

and dot_of_graph id in_gr =
  let { nmap = nm; eset = ne; symtab = _; typemap = _, _, _; w = _ } = in_gr in
  cate_nicer (dot_of_node_map id nm in_gr) (dot_of_edge_set id ne) "\n"

and write_dot_file in_gr =
  let oc = open_out "out.dot" in
  fprintf oc "%s" ("digraph R {\nnewrank=true;\n" ^ dot_of_graph 0 in_gr ^ "}");
  close_out oc;
  "Output Dot in out.dot"

and dot_graph in_gr =
  let na, oc = Filename.open_temp_file "graph-" ".dot" in
  fprintf oc "%s" ("digraph R {\nnewrank=true;\n" ^ dot_of_graph 0 in_gr ^ "}");
  close_out oc;

  print_endline ("Output Dot in " ^ na);
  ()

and write_any_dot_file sss in_gr =
  let oc = open_out sss in
  fprintf oc "%s" ("digraph R {\nnewrank=true;\n" ^ dot_of_graph 0 in_gr ^ "}");
  close_out oc;
  ()

and dot_of_node_ty id in_gr =
 fun n ->
  match n with
  | Literal (lab, _, str, _) ->
      string_of_int id ^ string_of_int lab ^ " [shape=plaintext;label=\"" ^ str
      ^ "\"]"
  | Simple (lab, n, _, _, prag) ->
      string_of_int id ^ string_of_int lab ^ " [shape=rect;label=\""
      ^ string_of_int lab ^ " "
      ^ cate_nicer (string_of_node_sym n) (string_of_pragmas prag) ":"
      ^ "\"]"
  | Compound (lab, _, _, pl, g, _) ->
      "subgraph cluster_" ^ string_of_int id ^ string_of_int lab ^ " {\n"
      ^ "label=\"" ^ string_of_int lab ^ " " ^ string_of_pragmas pl ^ "\";\n"
      ^ dot_of_graph (Hashtbl.hash (id, lab)) g
      ^ "\n" ^ "}"
  | Unknown_node -> "Unknown"
  | Boundary (_, yy, _, pp) ->
      "IN0" ^ string_of_int id ^ " [shape=rect;label=\""
      ^ cate_list (string_of_symtab_gr_in in_gr) "\\n"
      ^ "\"];\n" ^ "OUT0" ^ string_of_int id ^ " [shape=rect;label=\""
      ^ cate_list (string_of_symtab_gr_out in_gr) "\\n"
      ^ string_of_pair_list yy ^ string_of_pragmas pp ^ "\"]"

let intrinsic_lib =
  lazy
    (let in_gr =
       {
         nmap = NM.empty;
         eset = ES.empty;
         symtab = (SM.empty, SM.empty);
         typemap = (65536, TM.empty, MM.empty);
         w = 65536;
       }
       (* if node num start becoming this big we got a problem *)
       (* 4. Create the function signature objects *)
     in
     let all_2_1_lib_funs =
       List.map
         (fun ty_id ->
           Compound_type (Sisal_function_type ("", [ ty_id; ty_id ], [ ty_id ])))
         basic_type_list
     in
     let float_1_1_lib_funs =
       List.map
         (fun ty_id ->
           Compound_type (Sisal_function_type ("", [ ty_id ], [ ty_id ])))
         basic_float_list
     in
     let float_2_1_lib_funs =
       List.map
         (fun ty_id ->
           Compound_type (Sisal_function_type ("", [ ty_id; ty_id ], [ ty_id ])))
         basic_float_list
     in
     let all_1_1_lib_funs =
       List.map
         (fun ty_id ->
           Compound_type (Sisal_function_type ("", [ ty_id ], [ ty_id ])))
         basic_type_list
     in
     let int_1_1_lib_funs =
       List.map
         (fun ty_id ->
           Compound_type (Sisal_function_type ("", [ ty_id ], [ ty_id ])))
         basic_int_list
     in
     (* 5. Register and Collect IDs *)
     (* We use fold_left to thread the graph, but accumulate the resulting IDs *)
     let in_gr, added_type_1_1_ids =
       List.fold_left
         (fun (gr, ids) func_ty ->
           let (_, _, new_id), res_gr = add_sisal_type gr func_ty in
           (res_gr, new_id :: ids))
         (in_gr, []) all_1_1_lib_funs
     in
     let added_type_1_1_ids = List.rev added_type_1_1_ids in
     let in_gr, added_type_2_1_ids =
       List.fold_left
         (fun (gr, ids) func_ty ->
           let (_, _, new_id), res_gr = add_sisal_type gr func_ty in
           (res_gr, new_id :: ids))
         (in_gr, []) all_2_1_lib_funs
     in
     let added_type_2_1_ids = List.rev added_type_2_1_ids in
     let in_gr, added_float_type_1_1_ids =
       List.fold_left
         (fun (gr, ids) func_ty ->
           let (_, _, new_id), res_gr = add_sisal_type gr func_ty in
           (res_gr, new_id :: ids))
         (in_gr, []) float_1_1_lib_funs
       (* reverse because fold_left/cons flips the order *)
     in
     let added_float_type_1_1_ids = List.rev added_float_type_1_1_ids in
     let in_gr, added_float_type_2_1_ids =
       List.fold_left
         (fun (gr, ids) func_ty ->
           let (_, _, new_id), res_gr = add_sisal_type gr func_ty in
           (res_gr, new_id :: ids))
         (in_gr, []) float_2_1_lib_funs
       (* reverse because fold_left/cons flips the order *)
     in
     let added_float_type_2_1_ids = List.rev added_float_type_2_1_ids in
     let in_gr, added_int_type_1_1_ids =
       List.fold_left
         (fun (gr, ids) func_ty ->
           let (_, _, new_id), res_gr = add_sisal_type gr func_ty in
           (res_gr, new_id :: ids))
         (in_gr, []) int_1_1_lib_funs
     in
     let added_int_type_1_1_ids = List.rev added_int_type_1_1_ids in
     let (_, _, spl_case_dlexp), in_gr =
       add_sisal_type in_gr
         (Compound_type
            (Sisal_function_type ("", [ Ast.Double_real ], [ Ast.Long_ty ])))
     in
     let (_, _, spl_case_riexp), in_gr =
       add_sisal_type in_gr
         (Compound_type
            (Sisal_function_type ("", [ Ast.Real ], [ Ast.Integer ])))
     in
     let (_, _, spl_case_rirexp), in_gr =
       add_sisal_type in_gr
         (Compound_type
            (Sisal_function_type ("", [ Ast.Real; Ast.Integer ], [ Ast.Real ])))
     in
     let (_, _, spl_case_diexp), in_gr =
       add_sisal_type in_gr
         (Compound_type
            (Sisal_function_type
               ("", [ Ast.Double_real; Ast.Integer ], [ Ast.Double_real ])))
     in
     let (_, _, spl_case_hisexp), in_gr =
       add_sisal_type in_gr
         (Compound_type
            (Sisal_function_type ("", [ Ast.Half_ty ], [ Ast.Short_ty ])))
     in
     let vec_floor_trunc_pairs =
       [
         (Ast.Vec_ty Ast.Double2, Ast.Vec_ty Ast.Long2);
         (Ast.Vec_ty Ast.Double3, Ast.Vec_ty Ast.Long3);
         (Ast.Vec_ty Ast.Double4, Ast.Vec_ty Ast.Long4);
         (Ast.Vec_ty Ast.Double8, Ast.Vec_ty Ast.Long8);
         (Ast.Vec_ty Ast.Double16, Ast.Vec_ty Ast.Long16);
         (Ast.Vec_ty Ast.Float2, Ast.Vec_ty Ast.Int2);
         (Ast.Vec_ty Ast.Float3, Ast.Vec_ty Ast.Int3);
         (Ast.Vec_ty Ast.Float4, Ast.Vec_ty Ast.Int4);
         (Ast.Vec_ty Ast.Float8, Ast.Vec_ty Ast.Int8);
         (Ast.Vec_ty Ast.Float16, Ast.Vec_ty Ast.Int16);
         (Ast.Vec_ty Ast.Half2, Ast.Vec_ty Ast.Short2);
         (Ast.Vec_ty Ast.Half3, Ast.Vec_ty Ast.Short3);
         (Ast.Vec_ty Ast.Half4, Ast.Vec_ty Ast.Short4);
         (Ast.Vec_ty Ast.Half8, Ast.Vec_ty Ast.Short8);
         (Ast.Vec_ty Ast.Half16, Ast.Vec_ty Ast.Short16);
       ]
     in
     let in_gr, vec_floor_trunc_type_ids =
       List.fold_left
         (fun (gr, ids) (in_ty, out_ty) ->
           let (_, _, ty_id), gr =
             add_sisal_type gr
               (Compound_type (Sisal_function_type ("", [ in_ty ], [ out_ty ])))
           in
           (gr, ids @ [ (in_ty, out_ty, ty_id) ]))
         (in_gr, []) vec_floor_trunc_pairs
     in
     (* 6. Generate Mangled Names based on the same basic_type_list *)
     let lib_registry =
       List.combine
         (List.map
            (fun ty -> Ast.mangle_intrinsic "EXP" [ ty; ty ] [ ty ])
            basic_type_list)
         added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "BITWISE_AND" [ ty; ty ] [ ty ])
              basic_type_list)
           added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "BITWISE_OR" [ ty; ty ] [ ty ])
              basic_type_list)
           added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "BITWISE_XOR" [ ty; ty ] [ ty ])
              basic_type_list)
           added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "MOD" [ ty; ty ] [ ty ])
              basic_type_list)
           added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "MAX" [ ty; ty ] [ ty ])
              basic_type_list)
           added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "MIN" [ ty; ty ] [ ty ])
              basic_type_list)
           added_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "ATAN" [ ty; ty ] [ ty ])
              basic_float_list)
           added_float_type_2_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "ATAN" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "TAN" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "ASIN" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "ACOS" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "COS" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "LOG" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "LOG10" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "SQRTR" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "SQRT" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "SINH" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "COSH" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "TANH" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "RADIANS" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "DEGREES" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "ETOTHE" [ ty ] [ ty ])
              basic_type_list)
           added_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "ABS" [ ty ] [ ty ])
              basic_type_list)
           added_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "SQRT" [ ty ] [ ty ])
              basic_int_list)
           added_int_type_1_1_ids
       @ List.combine
           (List.map
              (fun ty -> Ast.mangle_intrinsic "SIN" [ ty ] [ ty ])
              basic_float_list)
           added_float_type_1_1_ids
       @ [
           ( Ast.mangle_intrinsic "EXP" [ Ast.Real; Ast.Integer ] [ Ast.Real ],
             spl_case_rirexp );
         ]
       @ [
           ( Ast.mangle_intrinsic "EXP"
               [ Ast.Double_real; Ast.Integer ]
               [ Ast.Double_real ],
             spl_case_diexp );
         ]
       @ [
           ( Ast.mangle_intrinsic "FLOOR" [ Ast.Double_real ] [ Ast.Long_ty ],
             spl_case_dlexp );
           ( Ast.mangle_intrinsic "FLOOR" [ Ast.Real ] [ Ast.Integer ],
             spl_case_riexp );
           ( Ast.mangle_intrinsic "FLOOR" [ Ast.Half_ty ] [ Ast.Short_ty ],
             spl_case_hisexp );
         ]
       @ [
           ( Ast.mangle_intrinsic "TRUNC" [ Ast.Double_real ] [ Ast.Long_ty ],
             spl_case_dlexp );
           ( Ast.mangle_intrinsic "TRUNC" [ Ast.Real ] [ Ast.Integer ],
             spl_case_riexp );
           ( Ast.mangle_intrinsic "TRUNC" [ Ast.Half_ty ] [ Ast.Short_ty ],
             spl_case_hisexp );
         ]
       @ List.concat_map
           (fun (in_ty, out_ty, ty_id) ->
             [
               (Ast.mangle_intrinsic "FLOOR" [ in_ty ] [ out_ty ], ty_id);
               (Ast.mangle_intrinsic "TRUNC" [ in_ty ] [ out_ty ], ty_id);
             ])
           vec_floor_trunc_type_ids
     in

     let in_gr =
       let add_basic_type_entry gr (id, t_def) =
         let m, td, tm = gr.typemap in
         {
           gr with
           typemap =
             (m, TM.add id t_def td, MM.add (rev_lookup_ty_name id) id tm);
         }
       in
       List.fold_left add_basic_type_entry in_gr basic_types
     in
     (* 7. Zip them together: (TypeID * MangledName) *)
     let _, ps = in_gr.symtab in
     let id = in_gr.w in
     let _, final_syms =
       List.fold_left
         (fun (id, local_symtab) (name, ty_id) ->
           ( id + 1,
             SM.add name
               { val_name = name; val_ty = ty_id; val_def = -1; def_port = 0 }
               local_symtab ))
         (id, ps) lib_registry
     in
     let { nmap = _; eset = _; symtab = _; typemap = _, final_types, _; w = _ }
         =
       in_gr
     in
     (final_syms, final_types))

let lookup_mangled_name name =
  let intrinsic_syms, _ = Lazy.force intrinsic_lib in
  SM.find_opt name intrinsic_syms

let lookup_mangled_type ty =
  let _, intrinsic_types = Lazy.force intrinsic_lib in
  TM.find_opt ty intrinsic_types

let lookup_partial_mangled_name target_prefix =
  let intrinsic_syms, _ = Lazy.force intrinsic_lib in
  SM.to_seq intrinsic_syms
  |> Seq.find (fun (name, _) -> String.starts_with ~prefix:target_prefix name)

let dump_typemap tm =
  let tm_entries = ref [] in
  TM.iter
    (fun id _ ->
      let full_desc = printable_full_type tm id in
      tm_entries :=
        sprintf "{ \"id\": %d, \"desc\": %s }" id full_desc :: !tm_entries)
    tm;
  let tm_json = sprintf "[%s]" (String.concat ", " (List.rev !tm_entries)) in
  Printf.printf "%s\n" tm_json

module If1_View = struct
  open Printf

  let esc s = "\"" ^ String.escaped s ^ "\""

  (* Helper to extract AST string specifically for the sidebar *)
  let extract_ast pragmas =
    List.fold_left
      (fun acc p -> match p with Ast_type s -> s | _ -> acc)
      "" pragmas

  (* Filters out Ast_type so it doesn't clutter the graph nodes *)
  let string_of_pragmas_no_ast p =
    List.fold_right
      (fun pr q ->
        let l =
          match pr with
          | Ast_type _ -> "" (* Moved to Sidebar *)
          | Bounds (i, j) -> sprintf "Bounds(%d,%d)" i j
          | SrcLine (i, j) -> sprintf "SrcLine(%d,%d)" i j
          | OpNum i -> "OpNum " ^ string_of_int i
          | Ar i -> "Ar " ^ string_of_int i
          | Of i -> "Of " ^ string_of_int i
          | Lazy -> "Lazy"
          | Name str -> "%na=" ^ str
          | Ref -> "Ref"
          | Pointer -> "Pointer"
          | Contiguous -> "Contiguous"
          | No_pragma -> ""
          | Subscript s -> "einsum:" ^ s
        in
        if l = "" then q else cate_nicer l q " ,")
      p ""

  let string_of_pragmas_no_name p =
    List.fold_right
      (fun pr q ->
        let l =
          match pr with
          | Ast_type _ -> ""
          | Name _ -> ""
          | Bounds (i, j) -> sprintf "Bounds(%d,%d)" i j
          | SrcLine (i, j) -> sprintf "SrcLine(%d,%d)" i j
          | OpNum i -> "OpNum " ^ string_of_int i
          | Ar i -> "Ar " ^ string_of_int i
          | Of i -> "Of " ^ string_of_int i
          | Lazy -> "Lazy"
          | Ref -> "Ref"
          | Pointer -> "Pointer"
          | Contiguous -> "Contiguous"
          | No_pragma -> ""
          | Subscript s -> "einsum:" ^ s
        in
        if l = "" then q else cate_nicer l q " ,")
      p ""

  (* Helper to extract Name pragma specifically *)
  let extract_name pragmas =
    List.fold_left (fun acc p -> match p with Name s -> s | _ -> acc) "" pragmas

  let rec render_node_to_json node =
    match node with
    | Simple (id, sym, pin, pout, prag) ->
        let label =
          sprintf "%s [%s]" (string_of_node_sym sym)
            (string_of_pragmas_no_name prag)
        in
        let name = extract_name prag in
        sprintf
          "{ \"id\": %d, \"type\": \"Simple\", \"label\": %s, \"value\": %s, \
           \"ports\": { \"in\": %s, \"out\": %s } }"
          id (esc label) (esc name)
          (esc (string_of_ports pin))
          (esc (string_of_ports pout))
    | Compound (id, sym, ty, prag, sub_gr, _) ->
        let label =
          sprintf "%s [%s]" (string_of_node_sym sym)
            (string_of_pragmas_no_name prag)
        in
        let ast = extract_ast prag in
        let name = extract_name prag in
        sprintf
          "{ \"id\": %d, \"type\": \"Compound\", \"label\": %s, \"value\": %s, \
           \"inner_type\": %d, \"subgraph\": %s }"
          id (esc label) (esc name) ty
          (render_graph_to_json ~ast sub_gr)
    | Literal (id, _, value, _) ->
        sprintf
          "{ \"id\": %d, \"type\": \"Literal\", \"value\": %s, \"label\": \"Literal\" }"
          id (esc value)
    | Boundary (_, _, _, prag) ->
        let label = sprintf "BOUNDARY [%s]" (string_of_pragmas_no_ast prag) in
        sprintf
          "{ \"id\": 0, \"type\": \"Boundary\", \"label\": %s, \"value\": \"\" }"
          (esc label)
    | _ -> "{ \"id\": -1, \"type\": \"Unknown\", \"value\": \"\", \"label\": \"Unknown\" }"

  and render_graph_to_json ?(ast = "") in_gr =
    let nodes =
      NM.to_seq in_gr.nmap
      |> Seq.map (fun (_, v) -> render_node_to_json v)
      |> List.of_seq
    in
    let e_list = ES.elements in_gr.eset in
    let is_err (_, _, tt) =
      match TM.find_opt tt (get_typemap_tm in_gr) with
      | Some (ERROR _) -> true
      | _ -> false
    in
    let err_es, data_es = List.partition is_err e_list in

    let data_edges = List.map (fun e -> esc (string_of_edge in_gr e)) data_es in
    let error_edges = List.map (fun e -> esc (string_of_edge in_gr e)) err_es in
    let syms = string_of_symtab_gr in_gr in
    let sym_json = sprintf "[%s]" (String.concat ", " (List.map esc syms)) in

    let _, tm, _ = in_gr.typemap in
    let tm_entries = ref [] in
    TM.iter
      (fun id _ ->
        let full_desc = printable_full_type tm id in
        tm_entries :=
          sprintf "{ \"id\": %d, \"desc\": %s }" id (esc full_desc)
          :: !tm_entries)
      tm;
    let tm_json = sprintf "[%s]" (String.concat ", " (List.rev !tm_entries)) in

    sprintf
      "{ \"nodes\": [%s], \"data_edges\": [%s], \"error_edges\": [%s], \
       \"symtab\": %s, \"typemap\": %s, \"ast\": %s }"
      (String.concat ", " nodes)
      (String.concat ", " data_edges)
      (String.concat ", " error_edges)
      sym_json tm_json (esc ast)

  let export_debug_html file_path in_gr =
    let oc = open_out file_path in
    let json_data = render_graph_to_json in_gr in

    (* 1. CSS & Header - One clean block *)
    fprintf oc "%s"
      "<html><head><style>\n\
      \      :root { --sidebar-width: 550px; --ast-height: 300px; }\n\
      \      body { \n\
      \        font-family: 'Menlo', monospace; font-size: 11px; background: \
       #1e1e1e; color: #d4d4d4; \n\
      \        margin: 0; display: grid; grid-template-columns: 1fr 5px \
       var(--sidebar-width); height: 100vh; \n\
      \        overflow: hidden; \n\
      \      }\n\n\
       .mermaid .edgeLabel rect {\n\
      \    fill: #2d2d2d !important;      /* Dark Gray/Black box */\n\
      \    stroke: #9370db !important;    /* Purple border to make it pop */\n\
      \    stroke-width: 1.5px !important;\n\
      \    rx: 2px;                       /* Very slight rounding for \
       sharpness */\n\
      \    opacity: 0.71 !important;         /* 100% solid, no softness */\n\
       }\n\n\
       .mermaid .edgeLabel {\n\
      \    color: #8b0000 !important;      /* Pure white text */\n\
      \    font-weight: 900 !important;   /* Extra Bold */\n\
      \    font-size: 13px !important;    /* Large enough to read easily */\n\
      \    font-family: 'Menlo', monospace;\n\
      \    text-shadow: none !important;  /* Remove all \"dreamy\" shadows */\n\
       }\n\n\
       /* 3. The Edges: Darker Green for better text overlay */\n\
       .mermaid path.edgePath {\n\
      \    stroke: #2d8a39 !important;    /* Solid Forest Green */\n\
      \    stroke-width: 2.5px !important;\n\
       }\n\
      \      #left-pane { overflow: auto; padding: 20px; border-right: 1px \
       solid #333; }\n\
      \      #resizer { cursor: col-resize; background: #333; transition: \
       background 0.2s; }\n\
      \      #resizer:hover { background: #569cd6; }\n\
      \      #right-pane { display: grid; grid-template-rows: 1fr 5px \
       var(--ast-height); background: #252526; height: 100vh; overflow: \
       hidden; }\n\
      \      #top-right { overflow-y: auto; display: flex; flex-direction: \
       column; }\n\
      \      #h-resizer { cursor: row-resize; background: #333; transition: \
       background 0.2s; z-index: 10; }\n\
      \      #h-resizer:hover { background: #569cd6; }\n\
      \      #ast-pane { overflow: auto; background: #1a1a1a; position: \
       relative; border-top: 1px solid #111; }\n\
      \      .tabs { position: sticky; top: 0; display: flex; background: \
       #2d2d2d; border-bottom: 1px solid #3e3e3e; z-index: 5; }\n\
      \      .tab { padding: 8px 15px; cursor: pointer; border-right: 1px \
       solid #3e3e3e; color: #888; }\n\
      \      .tab.active { background: #252526; color: #fff; border-bottom: \
       2px solid #569cd6; }\n\
       .ast-body { \n\
      \    color: #9cdcfe; \n\
      \    white-space: pre-wrap; /* This preserves \n\
      \ and wraps long lines */\n\
      \    font-family: 'Menlo', 'Monaco', monospace; \n\
      \    font-size: 11px; \n\
      \    padding: 15px; \n\
      \    display: inline-block;\n\
      \    min-width: 100%;       /* Ensures background covers the width */\n\
       }\n\
      \            .ast-header { position: sticky; top: 0; left: 0; \
       background: #111; color: #569cd6; font-weight: bold; padding: 8px 15px; \
       font-size: 10px; z-index: 4; border-bottom: 1px solid #333; display: \
       flex; justify-content: space-between; align-items: center; }\n\
      \      .pin-btn { cursor: pointer; padding: 2px 8px; border: 1px solid \
       #444; border-radius: 3px; background: #2d2d2d; color: #888; }\n\
      \      .pin-btn.active { background: #569cd6; color: #fff; border-color: \
       #fff; }\n\
      \      .graph-box { border-left: 1px solid #444; margin-left: 15px; \
       padding-left: 10px; }\n\
      \      summary { cursor: pointer; color: #569cd6; font-weight: bold; \
       padding: 2px; }\n\
      \      .node-item { color: #ce9178; margin: 1px 0; }\n\
      \      mark.highlight { background-color: #f0f000; color: #000; \
       font-weight: bold; }\n\
      \      #dag-modal { display: none; position: fixed; z-index: 100; left: \
       0; top: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.8); }\n\
      \      #dag-content { background: #1e1e1e; margin: 5% auto; padding: \
       20px; width: 90%; height: 80%; overflow: auto; border-radius: 8px; \
       border: 1px solid #444; }\n\
      \      .render-btn { font-size: 9px; cursor: pointer; background: \
       #3e3e3e; color: #b5cea8; border: 1px solid #555; border-radius: 3px; \
       margin-left: 10px; padding: 1px 4px; }\n\
      \      .render-btn:hover { background: #569cd6; color: #fff; }\n\
      \    </style></head><body>\n\
      \    <div id='left-pane'><h3>IF1 Hierarchy</h3><div id='root'></div></div>\n\
      \    <div id='resizer'></div>\n\
      \    <div id='right-pane'>\n\
      \      <div id='top-right'>\n\
      \        <div class='tabs'><div id='tab-sym' class='tab active' \
       onclick='switchTab(\"sym\")'>Symbols</div><div id='tab-tm' class='tab' \
       onclick='switchTab(\"tm\")'>TypeMap</div></div>\n\
      \        <div id='pane-content'>Select a Graph to see symbols</div>\n\
      \      </div>\n\
      \      <div id='h-resizer'></div>\n\
      \      <div id='ast-pane'>\n\
      \        <div class='ast-header'><span>AST ORIGIN</span><button \
       id='pin-ast' class='pin-btn' onclick='togglePin()'>Pin 📌</button></div>\n\
      \        <div id='ast-content' class='ast-body'>Select a Graph to view \
       AST origin...</div>\n\
      \      </div>\n\
      \    </div>\n\
      \    <div id='dag-modal' onclick='this.style.display=\"none\"'><div \
       id='dag-content' onclick='event.stopPropagation()'></div></div>\n\
      \    <script \
       src='https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js'></script>\n\
      \    <script>";

    fprintf oc "const data = %s;" json_data;

    fprintf oc "%s"
      "\n\
      \      let currentGraph = data;\n\
      \      let activeTab = 'sym';\n\
      \      let isPinned = false;\n\n\
      \      function togglePin() {\n\
      \        isPinned = !isPinned;\n\
      \        const btn = document.getElementById('pin-ast');\n\
      \        btn.classList.toggle('active', isPinned);\n\
      \        btn.textContent = isPinned ? 'Pinned 📍' : 'Pin 📌';\n\
      \      }\n\n\
      \      function switchTab(tab) {\n\
      \        activeTab = tab;\n\
      \        document.getElementById('tab-sym').classList.toggle('active', \
       tab === 'sym');\n\
      \        document.getElementById('tab-tm').classList.toggle('active', \
       tab === 'tm');\n\
      \        updateRightPane();\n\
      \      }\n\n\
      \      function updateRightPane() {\n\
      \        if (!isPinned) \
       document.getElementById('ast-content').textContent = currentGraph.ast \
       || 'No AST Pragma attached.';\n\
      \        const container = document.getElementById('pane-content');\n\
      \        container.innerHTML = '';\n\
      \        if (activeTab === 'sym') {\n\
      \          (currentGraph.symtab || []).forEach(s => {\n\
      \            const div = document.createElement('div'); div.textContent \
       = s; container.appendChild(div);\n\
      \          });\n\
      \        } else {\n\
      \          data.typemap.forEach(t => {\n\
      \            const div = document.createElement('div'); div.innerHTML = \
       `<span style='color:#4ec9b0'>[${t.id}]</span> ${t.desc}`; \
       container.appendChild(div);\n\
      \          });\n\
      \        }\n\
      \      }";

    fprintf oc "%s"
      "\n\
      \      async function renderDAG(graph) {\n\
      \        const modal = document.getElementById('dag-modal');\n\
      \        const content = document.getElementById('dag-content');\n\
      \  \n\
      \         // 1. Show modal and WIPE the old content entirely\n\
      \        modal.style.display = 'block';\n\
      \        content.innerHTML = ''; \n\
      \        // 2. Create a fresh PRE element\n\
      \        const pre = document.createElement('pre');\n\
      \        pre.className = 'mermaid';\n\
      \        pre.textContent = generateMermaidCode(graph);\n\
      \        content.appendChild(pre);\n\
      \      \n\
      \        // 3. The Secret Sauce: Wait 10ms\n\
      \        // This ensures the DOM has actually rendered the text \n\
      \        // before the Mermaid parser starts its work.\n\
      \        await new Promise(r => setTimeout(r, 10));\n\
      \        try {\n\
      \          // 4. Run specifically on the NEW element\n\
      \          await mermaid.run({\n\
      \            nodes: [pre]\n\
      \          });\n\
      \        } catch (err) {\n\
      \          console.error(\"Mermaid Error:\", err);\n\
      \          // If it fails, show the code so you can debug the syntax\n\
      \          content.innerHTML += `<div style=\"color:red;font-size:10px;\">\n\
      \                                  ${err.message}<br>\n\
      \                                  <pre>${pre.textContent}</pre>\n\
      \                                </div>`;\n\
      \        }\n\
      \      }";

    fprintf oc "%s"
      "\n\
      \      function generateMermaidCode(rootGraph) {\n\
      \        let lines = [\"---\\nconfig:\\nlayout: tidy-tree\\n---\\ngraph TD\"];\n\
      \        let edgeCount = 0;\n\
      \        function traverse(graph, prefix) {\n\
      \          (graph.nodes || []).forEach(n => {\n\
      \            const uid = prefix + n.id;\n\
      \            if (n.id === 0) {\n\
      \              lines.push(`  N${uid}_IN{{\"${prefix}Boundary IN\"}}`);\n\
      \              lines.push(`  N${uid}_OUT{{\"${prefix}Boundary OUT\"}}`);\n\
      \              lines.push(`  style N${uid}_IN fill:#1e2a1e,stroke:#b5cea8,stroke-width:2px,color:#b5cea8`);\n\
      \              lines.push(`  style N${uid}_OUT fill:#2a1e1e,stroke:#ce9178,stroke-width:2px,color:#ce9178`);\n\
      \            } else {\n\
      \              let labelPart = (n.label || \"\").trim();\n\
      \              if (labelPart === \"\" || labelPart === \"[]\") labelPart = n.type;\n\
      \              let text = labelPart.replace(/[\\[\\]\"{}]/g, \"\");\n\
      \              if (n.value && n.value !== n.label && n.value !== labelPart) {\n\
      \                text += \" (\" + n.value.replace(/[\\[\\]\"{}]/g, \"\") + \")\";\n\
      \              }\n\
      \              lines.push(`  N${uid}((\"${n.id}: ${text}\"))`);\n\
      \              if (n.subgraph) traverse(n.subgraph, uid + \"_\");\n\
      \            }\n\
      \          });\n\
      \          (graph.data_edges || []).forEach(e => {\n\
      \            const m = e.match(/(\\d+):(\\d+)\\s*->\\s*(\\d+):(\\d+)\\s*(.*)/);\n\
      \            if (m) {\n\
      \              const s = m[1] === \"0\" ? `N${prefix}0_IN` : `N${prefix}${m[1]}`;\n\
      \              const d = m[3] === \"0\" ? `N${prefix}0_OUT` : `N${prefix}${m[3]}`;\n\
      \              lines.push(`  ${s} -- \"p${m[2]}→p${m[4]}\\n${m[5]}\" --> ${d}`);\n\
      \              lines.push(`  linkStyle ${edgeCount++} stroke:#4ec9b0,stroke-width:2px`);\n\
      \            }\n\
      \          });\n\
      \        }\n\
      \        traverse(rootGraph, \"\");\n\
      \        return lines.join(\"\\n\");\n\
      \      }";

    fprintf oc "%s"
      "\n\
      \      function buildTree(container, graph, isRoot = false) {\n\
      \        const details = document.createElement('details');\n\
      \        details.open = isRoot;\n\
      \        const summary = document.createElement('summary');\n\
      \        summary.textContent = `Graph {${graph.nodes.length} nodes}`;\n\
      \        summary.onclick = (e) => { e.stopPropagation(); currentGraph = \
       graph; updateRightPane(); };\n\
      \        details.appendChild(summary);\n\n\
      \        const box = document.createElement('div'); \n\
      \        box.className = 'graph-box';\n\
      \        \n\
      \        graph.nodes.forEach(n => {\n\
      \          const d = document.createElement('div');\n\
      \          let labelPart = (n.label || \"\").trim();\n\
      \          if (labelPart === \"\" || labelPart === \"[]\") {\n\
      \            labelPart = n.type;\n\
      \          }\n\
      \          let nodeText = `Node ${n.id}: ${labelPart}`;\n\
      \          if (n.value && n.value !== n.label && n.value !== labelPart) {\n\
      \            nodeText += ` (${n.value})`;\n\
      \          }\n\
      \          if (n.subgraph) {\n\
      \            d.innerHTML = `<b>${nodeText}</b>`;\n\
      \            buildTree(d, n.subgraph, false);\n\
      \          } else {\n\
      \            d.className = 'node-item';\n\
      \            d.textContent = nodeText;\n\
      \          }\n\
      \          box.appendChild(d);\n\
      \        });\n\
      \        // Data Edges with DAG Button\n\
      \        const de = document.createElement('details'); de.open = true;\n\
      \        const deSum = document.createElement('summary');\n\
      \        deSum.style.color = '#b5cea8';\n\
      \        deSum.textContent = `Data Edges (${graph.data_edges.length})`;\n\
      \        \n\
      \        const btn = document.createElement('button');\n\
      \        btn.className = 'render-btn';\n\
      \        btn.textContent = 'Render DAG 🎨';\n\
      \        btn.onclick = (e) => { e.preventDefault(); e.stopPropagation(); \
       renderDAG(graph); };\n\
      \        \n\
      \        deSum.appendChild(btn);\n\
      \        de.appendChild(deSum);\n\
      \        graph.data_edges.forEach(e => { \n\
      \          const d = document.createElement('div'); \
       d.style.color='#b5cea8'; d.textContent='  ' + e; de.appendChild(d); \n\
      \        });\n\
      \        box.appendChild(de);\n\n\
      \        // Error Edges\n\
      \        const ee = document.createElement('details');\n\
      \        ee.innerHTML = `<summary style='color:#c62828'>Error Edges \
       (${graph.error_edges.length})</summary>`;\n\
      \        graph.error_edges.forEach(e => { \n\
      \          const d = document.createElement('div'); \
       d.style.color='#ff6b6b'; d.textContent='  ' + e; ee.appendChild(d); \n\
      \        });\n\
      \        box.appendChild(ee);\n\n\
      \        details.appendChild(box); \n\
      \        container.appendChild(details);\n\
      \      }\n\
      \      \n\
      \      // Resizer Logic (Vertical)\n\
      \      const vResizer = document.getElementById('resizer');\n\
      \      let isVResizing = false;\n\
      \      vResizer.onmousedown = () => { isVResizing = true; \
       document.body.style.userSelect = 'none'; };\n\n\
      \      // Resizer Logic (Horizontal)\n\
      \      const hResizer = document.getElementById('h-resizer');\n\
      \      let isHResizing = false;\n\
      \      hResizer.onmousedown = () => { isHResizing = true; \
       document.body.style.userSelect = 'none'; };\n\n\
      \      document.onmousemove = (e) => {\n\
      \        if (isVResizing) {\n\
      \          const width = window.innerWidth - e.clientX;\n\
      \          if (width > 150) \
       document.body.style.setProperty('--sidebar-width', width + 'px');\n\
      \        }\n\
      \        if (isHResizing) {\n\
      \          const height = window.innerHeight - e.clientY;\n\
      \          if (height > 50) \
       document.body.style.setProperty('--ast-height', height + 'px');\n\
      \        }\n\
      \      };\n\
      \      document.onmouseup = () => { isVResizing = isHResizing = false; \
       document.body.style.userSelect = 'auto'; };\n\n\
      \      buildTree(document.getElementById('root'), data, true);\n\
      \    </script></body></html>";
    close_out oc
end
