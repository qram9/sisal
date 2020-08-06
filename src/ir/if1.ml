(** GRAPH is best to build inside out, due to the
    language strictness that we need a node and ports
    tuple. AST visitor builds the GRAPH inside out.

    TESTS: we are able to look up nodes in IF1.NM
    with an integer

    TESTS: Edges are pairs of ints containing a
    pair of ints (node-id,port-id) for head of edge
    and one more pair for tail of edge. Finally all
    edges are typed, and we have an additional int for
    ty-id.

    Nodes are either
      | Simple of node-type (binary operators, for ex)
        (and a port array, that may hold an adjacency-list)
      | Compound nodes for subgraphs and graphs

    Node numbers must be unique only inside Graphs to allow
    for import/export.

    Graphs boundaries have some special properties. TODO: Description.


    Literal edges are 5 tuples:
    | Literal of dest node, port, ref to type label, string, comment

    TODO:

      Provide depth or breadth first visitors.

      Use adjacency lists on nodes for incoming/outgoing edges.

      Test type-id on edges.

      Add line number and file name for debug information.

   Label Scoping:
    TODO: Type must also be stored in the Top-level graph

  TODO: Need to see why we need create_subgraph_symtab
 *)


open Ast
open Format
open Printf
open Filename

(** TODO: FOLDING OF MULTIARITY SEEMS IFFY **)

module IntMap = Map.Make(
                    struct
                      type t = int
                      let compare = compare
                    end)

module IntSet = Set.Make(
                    struct
                      type t = int
                      let compare = compare
                    end)
module StringMap = Map.Make(
                    struct
                      type t = string
                      let compare = compare
                    end)

type label_or_none = Som of int | Emp

type node_sym =
  | BOUNDARY
  | CONSTANT
  | GRAPH
  | OLD
  | VAL
  | INVOCATION
  | NOT
  | NEGATE
  | ACATENATE
  | AND
  | DIVIDE
  | TIMES
  | SUBTRACT
  | ADD
  | OR
  | NOT_EQUAL
  | EQUAL
  | LESSER_EQUAL
  | LESSER
  | GREATER_EQUAL
  | GREATER
  | RBUILD
  | RELEMENTS
  | RREPLACE
  | SBUILD
  | SAPPEND
  | TAGCASE
  | SELECT
  | RANGEGEN
  | AADDH
  | AADDL
  | ABUILD
  | AELEMENT
  | AFILL
  | AGATHER
  | AISEMPTY
  | ALIML
  | ALIMH
  | AREPLACE
  | AREML
  | AREMH
  | ASCATTER
  | ASETL
  | ASIZE
  | INTERNAL
  | REDUCE
  | REDUCELEFT
  | REDUCERIGHT
  | REDUCETREE
  | STREAM
  | FINALVALUE
  | MULTIARITY

type comment =
  | C of string
  | CDollar of string

type basic_code =
  | BOOLEAN
  | CHARACTER
  | DOUBLE
  | INTEGRAL
  | NULL
  | REAL
  | ARRAY
  | RECORD
  | UNION
  | STREAM

type label = int

type if1_ty =
  | Array_ty of label
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
  | None

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
  let compare =
    Stdlib.compare
end

type port_idx = int

(**Edge module, to enable using Map and Set.
 Because no Fan-ins possible, each edge gets to be unique. *)
module E = struct
  type t = (N.t * port_idx) * (N.t * port_idx) * int
  let compare ((i,pi),(j,pj),_) ((k,pk),(m,pm),_) =
    let cv1 = compare i k in
    if cv1 = 0 then
      let cv2 = compare j m in
      if cv2 = 0 then
	let cv3 = compare pi pk in
	if cv3 = 0 then
	  let cv4 = compare pj pm in
	  cv4
	else
	  cv3
      else
	cv2
    else
      cv1
end

let rec find_port an_array curr_idx len elem =
  (** Look at an array of ints and locate elem in it.
   Throw an error, if elem is not found.*)
  if Array.get an_array curr_idx = elem
  then curr_idx
  else
    if curr_idx + 1 = len then
      raise (Node_not_found "Fail to find elem in array")
    else
      find_port an_array (curr_idx+1) len elem

let cate_nicer a b c =
  match b with
  |  "" -> a
  | _ ->
     match a with
     |  "" -> b
     | _ -> a ^ c ^ b

let rec cate_list a c =
  match a with
  | hd::tl ->
     cate_nicer hd (cate_list tl c) c
  | [] -> ""

and cate_list_pad i a c =
  match a with
  |  hd::tl ->
      cate_nicer
        ((String.make i ' ')^hd)
        (cate_list_pad i tl c) c
  | [] -> ""

module ES = Set.Make(E)

module NM = Map.Make(N)

module SM = Map.Make(String)

module MM = Map.Make(String)

module TM = Map.Make(T)

module AStrSet = Set.Make(String)

(** The graph datastructure used by If1: This record currently uses Map and Sets. I need to understand how this impacts performance to decide if other options like hashtab would be better. This record gets passed around heavily.

 The symbol table is a pair of maps, one for current level and one for parent level. It may be better to number the entries based on the hierarchy. It looks like other options like that may be better here. *)
type graph =
  {
    nmap : node NM.t;
    eset : ES.t ;
    symtab : (if1_value SM.t * if1_value SM.t);
    typemap : int * if1_ty TM.t * int MM.t;
    w : int
  }

(** Symbol table entry. *)
and if1_value =
  {
    val_ty : int;
    val_name : string;
    val_def : int;
    def_port : int;
  }

and node =
  | Simple of N.t * node_sym * ports * ports * pragmas
  | Compound of N.t * node_sym * label * pragmas * graph * N.t list
  | Literal of N.t * basic_code * string * ports
  | Boundary of (label * int * string ) list * (label * int) list * pragmas
  | Unknown_node

(** Create an empty graph for a caller. Take an incoming
    typemap and use that for the typemap. Make sure
    that the typemap has essential types, BOOLEAN, REAL etc.
    First symtab is current symtab and second for parent.
 *)
let rec get_empty_graph ty_blob =
  let nm = NM.add 0 (Boundary([],[],[]))  NM.empty in
  let in_gr =
    {
      nmap = nm;
      eset = ES.empty;
      symtab = (SM.empty, SM.empty);
      typemap = ty_blob;
      w = 1
    } in
  let _,in_gr =
    add_type_to_typemap (Basic BOOLEAN) in_gr in
  let _,in_gr =
    add_type_to_typemap (Basic REAL) in_gr in
  let _,in_gr =
    add_type_to_typemap (Basic CHARACTER) in_gr in
  let _,in_gr =
    add_type_to_typemap (Basic DOUBLE) in_gr in
  let _,in_gr =
    add_type_to_typemap (Basic INTEGRAL) in_gr in
  let _,in_gr =
    add_type_to_typemap (Basic NULL) in_gr in
  in_gr

and get_node_label n =
  match n with
  | Simple (x, _, _, _,_) -> x
  | Compound (x,_,_,_,_,_) -> x
  | Literal (x,_,_,_) -> x
  | Boundary _ -> 0
  | Unknown_node ->
     raise (Sem_error "Internal compiler error: unreachable @get_node_label")


(** Lookup a record field by name. *)
and get_record_field in_gr anum field_namen =
  let {nmap = _;eset = _;symtab = (_,_);
       typemap = (ti,tm,mm);w = _} = in_gr in
  let hasit = TM.mem anum tm in
  (match hasit with
   | true ->
      let rec_k = TM.find anum tm in
      (match rec_k with
       | Record (ff,nft,namen) ->
          (match (String.equal namen field_namen) with
           | true ->
              anum,ff
           | false ->
              get_record_field in_gr nft field_namen)
       | _ ->
          raise (Node_not_found
                   ("Could not locate record#:" ^
                      (string_of_int anum))))
   | false -> anum,0)

and get_graph_label
{nmap=_;eset=_;symtab=(_,_);typemap=_;w=i} = i

and get_graph_from_label ii
{nmap=nm;eset=_;symtab=(_,_);typemap=_;w=_} = match NM.find ii nm with
  | Compound (_,_,_,_,gg,_) -> gg
  | _ -> raise (Sem_error
                  "Internal compiler error: expected compound node for label.")

and has_node i
{nmap=nm;eset =_;symtab=(_,_);typemap=_;w=_} = NM.mem i nm

and get_node i
{nmap=nm;eset=_;symtab=(_,_);typemap=_;w=_} = NM.find i nm

(** Union cs into ps and set cs to empty. These things
 take a graph and return a graph.*)
and get_symtab_for_new_scope
{nmap=nm;eset=es;symtab=(cs,ps);typemap=tm;w=i} =
  {nmap=nm;eset=es;
   symtab=(SM.empty,SM.fold (fun k v z -> SM.add k v z) cs ps);
   typemap=tm;w=i}

(** Union other_ps, ps with other_cs.
    Then make it the new parent symtab with cs unchanged. *)
and inherit_parent_syms
{nmap=_;eset=_;symtab=(other_cs,other_ps);typemap=_;w=_}
{nmap=nm;eset=es;symtab=(cs,ps);typemap=tm;w=i} =
  {nmap=nm;eset=es;
   symtab=(cs,
           let kkk = fun k v z -> SM.add k v z in
           (SM.fold kkk other_cs (SM.fold kkk other_ps ps)));
   typemap=tm;w=i}

(** Weird case, where we copy local syms to other
only if they are not parent syms in other. *)
and create_subgraph_symtab
{nmap=_;eset=es;symtab=(cs,ps);typemap=otm;w=_}
{nmap=nm;eset=es;symtab=(other_cs,other_ps);typemap=tm;w=i} =
  let {nmap=nm;eset=es;
       symtab=(cs,ps); typemap=tm;w=i} =
    {nmap=nm;eset=es;
     symtab =
       (let kkk =
          fun k {val_name=vn_n;
                 val_ty=t1;val_def=_;def_port=_}
              (z,cou) ->
          if SM.mem k other_ps = false
          then
            (((SM.add k
              {val_name=vn_n;
               val_ty=t1;val_def=0;
               def_port=cou} z),cou+1))
          else
            (z,cou) in
        let other_cs,_ =
          SM.fold kkk cs (other_cs,SM.cardinal other_cs) in
        other_cs,other_ps);
     typemap=tm;w=i} in
  let port_name_map = SM.fold (fun k {val_name=_;
                                val_ty=_;val_def=_;
                                def_port=cou} zz ->
                          IntMap.add cou k zz) cs IntMap.empty in
  let rec make_a_small_lis x y alis =
    if x < y
    then
      make_a_small_lis (x+1) y ((0,x, IntMap.find x port_name_map)::alis)
    else
      alis in
  let boun_lis = make_a_small_lis 0 (SM.cardinal cs) [] in
  let in_gr =  {nmap = nm;eset = es;
                symtab = (cs,ps);
                typemap = merge_typeblobs tm otm;w = i} in
  let in_gr = input_from_boundary boun_lis in_gr in
  in_gr

and get_boundary_node {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} =
  NM.find 0 nm

and string_of_list_of_list alist_lis out_s =
  match alist_lis with
  | ahd::atl ->
     string_of_list_of_list atl
       ("[" ^ (String.concat ";"
                 (List.map (fun (_,y) -> string_of_int y)
                    ahd)) ^ "]")
  | _ -> out_s

and string_of_height_list height_list height_num =
  match height_list with
  | alis_lis::alis_tl ->
     cate_nicer
       ((string_of_int height_num) ^
          " : " ^ (string_of_list_of_list alis_lis ""))
       (string_of_height_list alis_tl (height_num+1))
       "\n"
  | [] -> ""

and string_of_5_ints (a,b,c,d,e) =
  (* Print a single predecessor, represented
       as a 5 tup *)
  "[" ^ (String.concat ";"
           ((string_of_node_sym
               (num_to_node_sym a))::
              (List.map string_of_int [b;c;d;e]))) ^ "]"

and string_of_pred_lis anod map_pred =
  (* Given a node number, print its predecessors *)
  if (IntMap.mem anod map_pred = true)
  then
    List.fold_left (
        fun zz cur ->
        cate_nicer
          zz
          ((string_of_5_ints cur))
          ";") "" (IntMap.find anod map_pred)
  else ""

and get_pred_lis anod map_pred =
  if (IntMap.mem anod map_pred = true)
  then
    List.fold_right
      (fun cur zz ->
        let a,b,c,d,e = cur in
        a::b::c::d::e::zz) (IntMap.find anod map_pred) [-1]
  else [anod;-1]

and sort_maps amap =
  (* Sort incoming edges by incoming port#, field#4*)
  let compare_5 (_,_,_,a,_) (_,_,_,b,_) =
    compare a b in
  IntMap.fold (
      fun ke va ret_map ->
      IntMap.add ke
        (List.sort compare_5 va) ret_map)
    amap IntMap.empty

and fold_pred_to_one_lis anod map_pred =
  if (IntMap.mem anod map_pred = true) then
    let pred_lis = IntMap.find anod map_pred in
    let pred_lis =
      List.fold_right (fun (a,b,c,d,e) zz ->
          a::b::c::d::e::-1::zz) pred_lis [] in
    pred_lis @ [-1;anod]
  else []

and append_or_add rev_h nod num =
  if (IntMap.mem num rev_h) = true
  then
    (IntMap.add num
       (IntSet.add nod (IntMap.find num rev_h))
       rev_h)
  else
    (IntMap.add num
       (IntSet.add nod IntSet.empty) rev_h)

and max_of_preds cur_max alis h rev_h map_pred cur_gr =
  match alis with
  | [] -> cur_max,h,rev_h
  | (_,ahd,_,_,_)::atl ->
     let h,rev_h = get_height
                     ahd map_pred h rev_h cur_gr in
     let ahd_h = IntMap.find ahd h in
     let cur_max,h,rev_h =
       if (cur_max < ahd_h)
       then
         (ahd_h,h,rev_h)
       else
         (cur_max,h,rev_h) in
     max_of_preds cur_max atl h rev_h map_pred cur_gr

and get_height cur map_pred h rev_h cur_gr =
  (if cur = 0
   then
     ((IntMap.add cur 0 h),
      (append_or_add rev_h cur 0))
   else
     (if (IntMap.mem cur h) = true
      then
        (h,rev_h)
      else
        (let cur_h,h,rev_h =
           if ((IntMap.mem cur map_pred) = false)
           then
             (0,h,rev_h)
           else
             (let ret_h,h,rev_h =
                (max_of_preds 0
                   (IntMap.find cur map_pred) h rev_h)
                  map_pred cur_gr in
              ret_h+1,h,rev_h) in
         IntMap.add cur cur_h h,
         append_or_add rev_h cur cur_h)))

and initialize_exp_info es nm =
  ES.fold
    (fun ((x,xp),(y,yp),ed_ty)
         (node_l,nm,init_height,map_succ,map_pred) ->
      let node_l,init_height =
        match IntMap.mem x init_height with
        | true -> node_l,init_height
        | false -> x::node_l, IntMap.add x 0 init_height in
      let xnm = NM.find x nm in
      let ynm = NM.find y nm in
      let xn = match xnm with
        | Simple (lab,n,_,_,_) -> n
        | Boundary _ -> BOUNDARY
        | Unknown_node ->
           raise (Sem_error "Internal, unreachable cse_height_xn")
        | Literal _ -> CONSTANT
        | Compound (lab, sy, ty, pl, g, assoc) -> GRAPH in

      let yn = match ynm with
        | Simple (lab,n,_,_,_) -> n
        | Boundary _ -> BOUNDARY
        | Literal _ -> CONSTANT
        | Unknown_node ->
           raise (Sem_error "Internal, unreachable cse_height_yn")
        | Compound (lab, sy, ty, pl, g, assoc) -> GRAPH in

      if xn != GRAPH && yn != GRAPH
      then
        (* True body when xn and yn are not GRAPHS *)
        let map_succ =
          match IntMap.mem x map_succ with
          | true ->
             IntMap.add x
               (((node_sym_to_num xn),xp,y,yp,ed_ty)::
                  (IntMap.find x map_succ)) map_succ
          | false ->
             IntMap.add x
               (((node_sym_to_num xn),xp,y,yp,ed_ty)::[])
               map_succ in
        let map_pred =
          match IntMap.mem y map_pred with
          | true ->
             IntMap.add y
               (((node_sym_to_num yn),x,xp,yp,ed_ty)::
                  (IntMap.find y map_pred)) map_pred
          | false ->
             IntMap.add y
               (((node_sym_to_num yn),x,xp,yp,ed_ty)::[])
               map_pred in
        let map_pred = sort_maps map_pred in
        let map_succ = sort_maps map_succ in
        (node_l,nm,init_height,map_succ,map_pred)
      else
        (* False Body when either xn and yn are GRAPHS.
           Not sure what to do here.*)
        (node_l,nm,init_height,map_succ,map_pred))
    (* ES.fold input *) es
    (* ES.fold output *) ([],nm,
                          IntMap.empty,
                          IntMap.empty,
                          IntMap.empty)
and visit_block ablk mymap (directory,capF) =
  match ablk with
  | (cur_pos,ahd)::atl ->
     let blk_content = IntMap.find ahd mymap in
     let nth = List.nth blk_content cur_pos in
     let directory =
       if (IntMap.mem nth directory = false) then
         (IntMap.add nth [(cur_pos,ahd)] directory)
       else
         (IntMap.add nth
            ((cur_pos,ahd)::(IntMap.find nth directory))
            directory) in
     let capF =
       if (IntSet.mem ahd capF = false)
       then (IntSet.add ahd capF)
       else capF in
     visit_block atl mymap (directory,capF)
  | [] ->
     directory,capF

and inc_pos alis =
  List.fold_right (fun (x,y) ou -> (x+1,y)::ou) alis []

and print_a_finished_one sentinel alis mymap =
  let string_of_int_pair (x,y) =
    "("^ (string_of_int (x+1)) ^ ","
    ^ (string_of_int y) ^
      " aka [" ^
        (String.concat "; "
           (List.map string_of_int
              (IntMap.find y mymap))) ^ "])" in
  (sentinel ^
     (String.concat ";"
        (List.map (string_of_int_pair) alis)) ^ "\n")

and get_vn_table alis cur outm =
  (** Each entry in alis is value-numbered to the
      witness named cur. *)
  match alis with
  | (_,hd)::tl ->
     get_vn_table tl cur (IntMap.add hd cur outm)
  | [] -> outm

and update_a_list ahd vns =
  List.map
    (fun x ->
      if IntMap.mem x vns = true then
        (IntMap.find x vns)
      else x) ahd

and update_vns ablk vns new_mymap =
  match ablk with
  | (cur_pos,ahd)::atl ->
     let updated_map = (* output map *)
       IntMap.add
         ahd (* key *)
         (update_a_list
            (IntMap.find ahd new_mymap) vns) (* value *)
         new_mymap (* input map *)in
     update_vns atl vns updated_map
  | [] -> new_mymap

and visit_block_list blks vns mymap =
  (** This is the inner function that calls
      visit_block for each blocks in the blks list
      to see if they are finished. *)
  match blks with
  | ahd::atl ->
     let ff,capF =
       visit_block ahd (update_vns ahd vns mymap)
         (IntMap.empty, IntSet.empty) in
     (** Figure out the cases that finished
        and cases that are still being updated. *)
     let not_yet_done,done_ones =
       IntMap.fold (fun ke valu (not_done,all_done) ->
           if ke = -1
           then
             (not_done,
              ( let _,s = List.hd valu in
                print_string
                  ("(REACHED SENTINEL) WITNESS:" ^
                     (string_of_int s) ^ " FOR " ^
                       (string_of_int (List.length valu)) ^
                         " TREES" ^
                           (print_a_finished_one " :- " valu mymap));
                get_vn_table valu s all_done))
           else if List.length valu = 1
           then
             (not_done,
              (print_string
                 (print_a_finished_one "SIZE 1 :- " valu mymap);
               let _,s = List.hd valu in
               print_endline ("WITNESS:" ^ (string_of_int s));
               get_vn_table valu s all_done))
           else
             ((inc_pos valu)::not_done,all_done)) ff ([],vns) in
     let to_follow = atl@not_yet_done in
     visit_block_list to_follow done_ones mymap
  | [] -> vns

and visit_by_height mymap height_list vns height_num =
  (** We have a block list at each height. This function
      traverses by height (0,N) and calls visit_block at each. *)
  match height_list with
  | alis::tl ->
     print_endline ("-------------------");
     print_endline ("At Height:" ^
                      (string_of_int height_num));
     let vns = visit_block_list alis vns mymap in
     visit_by_height mymap tl vns (height_num+1)
  | [] -> vns

and cse_by_part in_gr =
  (* Each edge starts at a node,port and
     ends at another node,port.
      (x,xp) -> (y,yp), with type ed_ty:
      (x,xp,y,yp,ed_ty).
      Pred of y, is a reversing of the arrow
      or by adjusting the tuple like this:
      (yp,x,xp,ed_ty):
      incoming port is yp, src# is x,
      src out-port is xp, type ed_ty.
      Similarly, for each x, the tuples
      that describe the arrow
      going out is (xp,y,yp,ed_ty).
      That shall be used along with the
      opcode, xn, to describe the outgoing edge.
      Similarly, (yn,y,yp,xp,ed_ty) will
      describe a succ-edge with the node-type
      of y: yn. Suppose we have a binary
      operation, for ex,
      opcode:ADD,
      Preds:
      Op1:(xp1,y1,yp1,ed_ty)
      Op2:(xp2,y2,yp2,ed_ty).
      Folding the tree to a list gives:
      [ADD;xp1;y1;yp1;ed_ty;xp2;y2;yp2;ed_ty]
      A duplicate operation needs to have the
      same content as above.
      TODO: How do we do this for calls?!?
      Must we have a compare function that
      accepts a node-sym variant?
      1:A height relation is first obtained.
      The height relation function is called
      get_height. It would start with
      the height of incoming boundary node to 0.
      Then the height of internal nodes are
      calculated by getting the max of children
      heights, with a recursive walk that
      ends on the outgoing boundary node,
      again numbered 0.
      2:The cse algorithm operates from
      inner-most graphs outwards,
      in post-order. The top-level is called
      cse_by_part. For each graph,
      CSE goes up the height relation
      and DAGifys, that is, it provides
      value numbers to each of the
      unique trees at a current
      height. Height is incremented,
      but before processing the nodes
      at the incremented height,
      the vn table must be checked and
      current lists updated.*)
  let {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} = in_gr in
  let nm =
    NM.fold
      (fun lab nod last_nm ->
        let last_nm = match nod with
          | Simple (lab,n,_,_,_) ->
             last_nm
          | Boundary _ ->
             last_nm
          | Unknown_node ->
             raise (Sem_error "Internal, unreachable cse_height_xn")
          | Literal _ -> last_nm
          | Compound (lab, sy, ty, pl, subgr, assoc) ->
             let subgr = cse_by_part subgr in
             NM.add lab
               (Compound (lab,sy,ty,pl,subgr,assoc)) last_nm in
        last_nm) nm nm in
  let node_l,nm,init_height,map_succ,map_pred = initialize_exp_info es nm in
  let cur_gr = {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} in
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
  let height_map,rev_height_map =
    List.fold_left
      (fun (height_map,rev_h) cur ->
        get_height cur map_pred height_map rev_h cur_gr)
      (IntMap.empty,IntMap.empty) node_l in
  (*print_endline
    ("Height:\n" ^
       (IntMap.fold (
            fun nod h z ->
            (string_of_int nod) ^
              " -> " ^ (string_of_int h) ^ "\n" ^ z)
          height_map ""));*)
  let nodes_by_height =
    IntMap.bindings rev_height_map in
  let my_lis_lis =
    (List.fold_right
       (fun (x,set) last_lis ->
         [(List.map
             (fun x -> (0,x))
             (IntSet.elements set))]::last_lis)
       nodes_by_height []) in
  let mymap =
    IntMap.fold
      (fun x h last_m ->
        IntSet.fold
          (fun cur last_map ->
            IntMap.add cur
              (get_pred_lis cur map_pred)
              last_map) h last_m) rev_height_map IntMap.empty in
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
  let rev_height_map_folded =
    IntMap.fold (
        fun nod ed z ->
        IntMap.add nod
          (IntSet.fold
             (fun cur yy ->
               let folded_lis =
                 fold_pred_to_one_lis cur map_pred in
               folded_lis::yy)
             ed []) z) rev_height_map IntMap.empty in
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
    (IntMap.fold (fun x y las ->
         let x,y = string_of_int x, string_of_int y in
         String.concat "\n"
           [(String.concat " -> " [x; y]); las])
       vns "");
  let es =
    ES.fold (fun ((x,xp),(y,yp),y_ty) res ->
        let x =
          if IntMap.mem x vns = true
          then
            IntMap.find x vns
          else
            x in
        ES.add ((x,xp),(y,yp),y_ty) res)
      es ES.empty in
  let res_gr =
    {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} in
  let ll = dot_graph res_gr in
  res_gr

and add_to_boundary_outputs ?(start_port=0) srcn srcp tty in_gr =
  match get_boundary_node in_gr with
  | (Boundary (in_port_list,out_port_list,boundary_p)) ->
     let {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} =
       in_gr in
     let annod = NM.find srcn nm in
     let annod =
       (match annod with
        | Simple (lab,n,pin,pont,prag) ->
           let mylis = Array.to_list pont in
           let mylis = (string_of_int 0)::mylis in
           Simple (lab,n,pin,(Array.of_list mylis),prag)
        | _ -> annod) in
     let start_port =
       if start_port = 0
       then List.length out_port_list
       else start_port in
     (add_edge2 srcn srcp 0 start_port tty
        {nmap=NM.add 0
                (Boundary
                   (in_port_list,
                    (srcn,srcp)::out_port_list,boundary_p))
                (NM.add srcn annod nm);
         eset=es;symtab=sm;typemap=tm;w=pi})
  | _ -> in_gr

and get_named_input_ports in_gr =
  match get_boundary_node in_gr with
  |  (Boundary (in_port_list,out_port_list,boundary_p)) ->
      in_port_list
  | _ -> []

and get_named_input_port_map in_gr =
  match get_boundary_node in_gr with
  |  (Boundary (in_port_list,out_port_list,boundary_p)) ->
      List.fold_right (fun (xx,yy,zz) output_map ->
          StringMap.add zz yy output_map) in_port_list StringMap.empty
  | _ -> StringMap.empty

and add_to_boundary_inputs ?(namen="") n p in_gr =
  match get_boundary_node in_gr with
  | (Boundary (in_port_list,out_port_list,boundary_p)) ->
     let lookin_lis n p =
       try
         List.fold_right (
             fun (x,y,z) res ->
             if n = x && p = y
             then
               raise (Val_is_found x)
             else res) in_port_list false
       with Val_is_found x -> true in

     if (lookin_lis n p) = true then in_gr
     else
       (let {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} =
          in_gr in
        {nmap=NM.add 0
                (Boundary ((n,p,namen)::in_port_list,
                           out_port_list,boundary_p))
                nm;
         eset=es;symtab=sm;typemap=tm;w=pi})
  | _ -> in_gr

and boundary_in_port_count in_gr =
  match get_boundary_node in_gr with
  | (Boundary (in_port_list,out_port_list,boundary_p)) ->
     List.length in_port_list
  | _ -> 0

and boundary_out_port_count in_gr =
  match get_boundary_node in_gr with
  | (Boundary (in_port_list,out_port_list,boundary_p)) ->
     List.length out_port_list
  | _ -> 0

and get_old_var_port vv =
  function
    {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} ->
    let old_name =  ("OLD " ^ vv) in
    if SM.mem old_name cs = true then
      let {val_name=vn;val_ty=tt;
           val_def=def;def_port=cou} =
        (SM.find old_name cs) in
      `Found_one cou
    else `Not_there

and defs_of_bound_names =
  function
    {nmap=nm;eset=pe;symtab=(cs,ps);typemap=tm;w=pi} ->
    SM.fold
      (fun k
           {val_name=vn;val_ty=tt;
            val_def=def;def_port=cou} xx ->
        IntMap.add def k xx) cs IntMap.empty

and output_bound_names_for_subgraphs ?(start_port=0) alis in_gr =
  let bound_ports = defs_of_bound_names in_gr in
  let alis,in_gr =
    List.fold_right
      (fun (x,y,z) (yy,in_gr_) ->
        if IntMap.mem x bound_ports then
          match get_old_var_port (IntMap.find x bound_ports) in_gr with
          | `Not_there -> (x,y,z)::yy,in_gr_
          | `Found_one cou ->
             yy,add_edge2 x y 0 cou z in_gr_
        else (x,y,z)::yy,in_gr_) alis ([],in_gr) in
  output_to_boundary ~start_port:(boundary_out_port_count in_gr) alis in_gr

and output_to_boundary ?(start_port=0) alis in_gr =
  match alis with
  | (srcn,srcp,tyy)::tl ->
     let srcn,srcp,tyy =
       find_incoming_regular_node (srcn,srcp,tyy) in_gr in
     output_to_boundary tl
       (add_to_boundary_outputs ~start_port:start_port
          srcn srcp tyy in_gr)
  | [] ->
     in_gr

and output_to_boundary_with_none ?(start_port=0) alis in_gr =
  match alis with
  | (Some (srcn,srcp,tyy))::tl ->
     let srcn,srcp,tyy = find_incoming_regular_node (srcn,srcp,tyy) in_gr in
     output_to_boundary_with_none tl
       (add_to_boundary_outputs ~start_port:start_port
          srcn srcp tyy in_gr)
  | None::tl ->
     output_to_boundary_with_none tl in_gr
  | [] -> in_gr

and input_from_boundary alis in_gr =
  match alis with
  | (srcn,srcp,nam)::tl ->
     input_from_boundary tl
       (add_to_boundary_inputs ~namen:nam srcn srcp in_gr)
  | [] -> in_gr

and string_of_pair_int (x,y) =
  "("^ (string_of_int x) ^ "," ^ (string_of_int y) ^ ")"

and safe_set_arr str po arr =
  if Array.length arr < po then
    ((arr.(po) <- (arr.(po) ^ (str)));arr)
  else
    (Array.of_list ((Array.to_list arr)@[str]))

and set_out_port_str src_nod src_port dest_nn =
  match src_nod with
  | Literal (lab,ty,str,pout) ->
     Literal (lab,ty,str,safe_set_arr dest_nn src_port pout)
  | Simple (lab,n,pin,pout,prag) ->
     Simple (lab,n,pin,safe_set_arr dest_nn src_port pout,prag)
  | Compound (lab, sy, ty, pl, g, assoc) ->
     src_nod
  | Boundary (_,_,p) -> src_nod
  | Unknown_node -> src_nod

and clear_port_str dst_nod =
  match dst_nod with
  | Literal (lab,ty,str,pout) ->
     let kk = Array.make 1 "" in
     Literal (lab,ty,str,kk)
  | Simple (lab,n,pin,pout,prag) ->
     let kk = Array.make 1 "" in
     let ll = Array.make 1 "" in
     Simple (lab,n,kk,ll,prag)
  | Compound (lab,sy,ty, pl, g, assoc) ->
     dst_nod
  | Boundary _ -> dst_nod
  | Unknown_node -> dst_nod

and set_in_port dst_nod dst_port src_nn =
  match dst_nod with
  | Literal (lab,ty,str,pout) ->
     dst_nod
  | Simple (lab,n,pin,pout,prag) ->
     if pin.(dst_port) != "" then
       raise (Node_not_found "in_port set already")
     else
       Simple (lab,n,safe_set_arr src_nn dst_port pin,pout,prag)
  | Compound (lab, sy,ty, pl, g, assoc) ->
     dst_nod
  | Boundary _ -> dst_nod
  | Unknown_node -> dst_nod

and set_in_port_str dst_nod dst_port src_str =
  match dst_nod with
  | Literal (lab,ty,str,pout) ->
     dst_nod
  | Simple (lab,n,pin,pout,prag) ->
     Simple (lab,n,safe_set_arr src_str dst_port pin,pout,prag)
  | Compound (lab,sy,ty, pl, g, assoc) ->
     dst_nod
  | Boundary _ -> dst_nod
  | Unknown_node -> dst_nod

and set_literal dst_nod dst_port src_node =
  match src_node with
  | Literal (_,_,str_,_) ->
     (match dst_nod with
      | Literal (lab,ty,str,pout) ->
         dst_nod
      | Simple (lab,n,pin,pout,prag) ->
         Simple (lab,n,
                 (pin.(dst_port) <- "Literal:" ^ str_;pin),
                 pout,prag)
      | Compound (lab, sy, ty, pl, g, assoc) ->
         dst_nod
      | Boundary _ -> dst_nod
      | Unknown_node -> dst_nod)
  | _ -> dst_nod

and add_node nn
{nmap = nm;eset = pe;symtab = (par_cs,par_ps);typemap = tm;w = pi} =
  match nn with
  | `Simple (n,pin,pout,prag) ->
     {nmap = NM.add pi (Simple(pi,n,pin,pout,prag)) nm;
      eset = pe;symtab = (par_cs,par_ps);typemap = tm;w = pi+1}
  | `Compound (g,sy,ty,prag,alis) ->
     let {nmap = gnm;eset = ges;
          symtab = (child_cs,child_ps);typemap = _;w = g_w} = g in
     let g_tmn = get_types_from_graph g tm in
     let g = {nmap = gnm; eset=ges;symtab = (child_cs,child_ps);
              typemap=g_tmn;w=g_w} in
     let par_ps = SM.fold (fun k v z -> SM.add k v z) child_ps par_ps in
     {nmap = NM.add pi (Compound(pi,sy,ty,prag,g,alis)) nm;
      eset = pe;symtab = (par_cs,par_ps);typemap = g_tmn;w = pi+1}
  | `Literal (ty_lab,str,pout) ->
     {nmap = NM.add pi (Literal(pi,ty_lab,str,pout)) nm;
      eset = pe;symtab = (par_cs,par_ps);typemap = tm;w = pi+1}
  | `Boundary ->
     {nmap = NM.add 0 (Boundary([],[],[])) nm;
      eset = pe;symtab = (par_cs,par_ps);typemap = tm;w = pi;}

and lookup_tyid = function
  | BOOLEAN -> 1
  | CHARACTER -> 2
  | REAL -> 3
  | DOUBLE -> 4
  | INTEGRAL -> 5
  | NULL -> 6
  | _ -> 7

and rev_lookup_ty_name = function
  | 1 -> "BOOLEAN"
  | 2 -> "CHARACTER"
  | 3 -> "REAL"
  | 4 -> "DOUBLE"
  | 5 -> "INTEGRAL"
  | 6 -> "NULL"
  | _ -> "UNKNOWN"

and lookup_fn_ty fff in_gr =
  let { nmap = nm; eset = pe; symtab = sm;
        typemap = (id,tm,tmn); w = pi; } =  in_gr in
  try
    TM.fold
      (fun ke va z ->
        match va with
        | Function_ty (args_ty,ret_ty,fn_name) ->
           (if fn_name = fff then
              (
                let tm_l =
                  let rec fold_ret_ty_lis ret_ty =
                    match TM.find ret_ty tm with
                    | Tuple_ty (fty,nty) ->
                       if (nty = 0) then
                         [fty]
                       else
                         fty::(fold_ret_ty_lis nty)
                    | _ -> raise (Sem_error "Incorrect function type in") in
                  fold_ret_ty_lis ret_ty in
                raise (List_is_found tm_l))
            else z)
        | _ -> z) tm []
  with List_is_found tml -> tml

and add_node_2 nn
{nmap = nm;eset = pe;symtab = sm;typemap = tm;w = pi} =
  match nn with
  | `Simple (n,pin,pout,prag) ->
     (pi,0,0),
     {nmap =
        NM.add pi
	  (Simple(pi,n,pin,pout,prag)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
  | `Compound (g,sy,ty,prag,alis) ->
     let g_tmn = get_types_from_graph g tm in
     let {nmap = gnm; eset=ges;symtab = (child_cs,child_ps);
          typemap=_;w=g_w} = g in
     let g = {nmap = gnm; eset=ges;symtab = (child_cs,child_ps);
              typemap=g_tmn;w=g_w} in
     (pi,0,0),
     {nmap =
        NM.add pi
	  (Compound(pi,sy,ty,prag,g,alis)) nm;
      eset = pe;symtab = sm;typemap = g_tmn;w = pi+1}
  | `Literal (ty_lab,str,pout) ->
     (pi,0,lookup_tyid ty_lab),
     {nmap =
        NM.add pi (Literal(pi,ty_lab,str,pout)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
  | `Boundary ->
     (pi,0,0),
     {nmap=NM.add 0 (Boundary([],[],[])) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}

and add_edge2 n1 p1 n2 p2 ed_ty
{nmap = nm;eset = pe;symtab = sm;typemap = tm;w = pi} =
  {nmap = nm;eset=ES.add ((n1,p1),(n2,p2),ed_ty) pe;
   symtab = sm;typemap = tm;w = pi;}

and fix_incoming_multiarity n1 p1 n2 p2 aty in_gr =
  let {nmap = nm;eset=pe;symtab=(cs,ps);typemap=tm;w=pi} = in_gr in
  match (NM.find n1 nm) with
  | Simple(_,MULTIARITY,_,_,_) ->
     let ending_at = all_edges_ending_at_port n1 p1 in_gr in
     let nes =
       if (ES.cardinal ending_at != 1) then
         raise (Sem_error "Incoming problem")
       else
         (let nending_at =
            ES.fold (fun ((x,xp),(y,yp),y_ty) res ->
                ES.add ((x,xp),(n2,p2),y_ty) res)
              ending_at ES.empty in
          ES.union
            (ES.remove ((n1,p1),(n2,p2),aty) pe)
            nending_at) in
     {nmap=nm;eset=nes;symtab=(cs,ps);typemap=tm;w=pi}
  | _ -> in_gr

and all_edges n1 n2 in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter
                (fun ((x,xp),(y,yp),y_ty) ->
                  x=n1 && y=n2) pe in edges

and all_edges_ending_at_port n2 p2 in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter
                (fun ((x,xp),(y,yp),y_ty) ->
                  y=n2 && yp = p2) pe in
  edges

and all_edges_ending_at n2 in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter
                (fun ((x,xp),(y,yp),y_ty) ->
                  y=n2) pe in
  edges

and all_edges_ending_at_ports_types n2 in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter
                (fun ((x,xp),(y,yp),y_ty) ->
                  y=n2) pe in
  ES.fold (fun ((x,xp),(y,yp),y_ty) z -> (xp,y_ty)::z) edges []

and all_nodes_joining_at (n2,np,ed_ty) in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter
                (fun ((x,xp),(y,yp),y_ty) ->
                  y=n2) pe in
  List.fold_right (fun ((x,xp),(y,yp),y_ty) zz ->
      (x,xp,y_ty)::zz) (ES.elements edges) []

and all_types_ending_at n2 in_gr res =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let map_tnem =
    ES.fold
      (fun ((x,xp),(y,yp),y_ty) acc ->
        if y=n2 then
          (IntMap.add yp y_ty acc) else acc) pe res in
  map_tnem

and connect_one_to_one in_lis to_n in_gr =
  let in_gr,_ =
    List.fold_right (
        fun (n1,p1,y_ty) (zzz,p2) ->
        add_edge n1 p1 to_n (p2+1) y_ty zzz,p2+1)
      in_lis (in_gr,0) in
  in_gr

and all_edges_starting_at n1 in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter
                (fun ((x,xp),(y,yp),y_ty) ->
                  x=n1) pe in
  edges

and check_for_multiarity n1 n2 in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  match (NM.find n1 nm) with
  | Simple(_,MULTIARITY,_,_,_) ->
     (match (NM.find n2 nm) with
         | Simple(_,MULTIARITY,_,_,_) ->
            true
         | _ -> false)
  | _ -> false

and cleanup_multiarity in_gr =
  let {nmap = nm;eset=es;symtab=sm;typemap=tm;w=pi} = in_gr in
  let new_nm = NM.fold (fun x y z -> match y with
               | Simple (_,MULTIARITY,_,_,_) -> z
               | Compound (pi,sy,ty,prag,g,alis) ->
                   NM.add x (Compound(pi,sy,ty,prag,
                             cleanup_multiarity g,alis)) z
               | _ -> NM.add x y z) nm NM.empty in
  let new_edges = ES.filter (fun ((x,xp),(y,yp),y_ty) ->
                  NM.mem y new_nm = true) es in
  {nmap=new_nm;eset=new_edges;symtab=sm;typemap=tm;w=pi}


and remove_edge n1 p1 n2 p2 ed_ty in_gr =
  (*Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);*)
  let {nmap=nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  {nmap = nm;
   eset = ES.remove ((n1,p1),(n2,p2),ed_ty) pe;
   symtab = sm;typemap = tm;w = pi;}

and add_from_edge ((n1,p1),(n2,p2),ed_ty) in_gr =
  add_edge n1 p1 n2 p2 ed_ty in_gr

and node_incoming_at_port n1 p in_gr =
  let edges = ES.elements (all_edges_ending_at_port n1 p in_gr) in
  if List.length edges > 1 then
    raise (Sem_error ("Only one fan-in being violated"))
  else
    try
      let (x,y),(u,v),ty = List.hd edges in (x,y,ty)
    with _ ->
      write_any_dot_file "ERROR.dot" in_gr;
      print_string ("Error when looking up node incoming to port");
      print_int p;print_char '\n';
      print_endline (string_of_graph in_gr);
      Printexc.print_raw_backtrace stdout (Printexc.get_callstack 20);
      raise (Sem_error ("Failing with node incoming at port:" ^
		          (string_of_int n1) ^ "," ^ (string_of_int p)))

and find_incoming_regular_node (n1, p1, ed_ty) in_gr =
  match get_node n1 in_gr with
  | Simple (_,MULTIARITY,_,_,_) ->
     let n1,p1,ed_ty =
       node_incoming_at_port n1 p1 in_gr in
     find_incoming_regular_node (n1, p1, ed_ty) in_gr
  | _ -> n1,p1,ed_ty

and add_edge n1 p1 n2 p2 ed_ty in_gr =
  (*print_endline "Calltrace:";
  Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);*)

  let n1,p1,ed_ty = find_incoming_regular_node (n1, p1, ed_ty) in_gr in
  if n2 = 0
  then
    (add_to_boundary_outputs ~start_port:p2 n1 p1 ed_ty in_gr)
  else
    (let in_gr =
       (if n1 = 0
        then
          add_to_boundary_inputs 0 p1 in_gr
        else
          in_gr) in

     let in_gr = add_edge2 n1 p1 n2 p2 ed_ty in_gr in
      in_gr)

and redirect_edges n2 es =
  ES.fold (fun hde (res,p2) ->
      let (x,xp),(y,yp),yt = hde in
      (ES.add ((x,xp),(n2,p2),yt) res),p2+1) es (ES.empty,0)

and incoming_arity n1 in_gr =
  let edges = all_edges_ending_at n1 in_gr in
  ES.cardinal edges

and outgoing_arity n1 in_gr =
  let edges = all_edges_starting_at n1 in_gr in
  ES.cardinal edges

and fold_multiarity_edge n1 n2 in_gr =
  let edges = all_edges n1 n2 in_gr in
  let ending_at = (all_edges_ending_at n1 in_gr) in
  let redir_set,_ = redirect_edges n2
                    (ES.diff ending_at edges) in
  let { nmap = nm;
        eset = es;
        symtab = sm;typemap = tm;w = pi; } = in_gr in
  let es = ES.union
             redir_set in
  let  { nmap = nm; eset = es;
         symtab = sm;typemap = tm;w = pi; } =
    ES.fold (
        fun ((x,xp),(y,yp),yt) gr ->
        add_edge x xp y yp yt gr) redir_set in_gr in
  let es = (ES.diff (ES.diff es ending_at) edges) in
  let in_gr =  { nmap = nm; eset = es;
                 symtab = sm;typemap = tm;w = pi; } in
  in_gr

and add_each_in_list in_gr ex lasti appl =
  match ex with
  | [] -> ((lasti,0,0),in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ =
       (appl in_gr hde) in
     add_each_in_list in_gr_ tl lasti appl

and range a b =
  (if a >= b then []
  else a :: range (a+1) b)

and add_edge_multiarity in_n in_p out_n out_p tt1 in_gr =
  match get_node in_n in_gr with
  | Simple(_,MULTIARITY,_,_,_) ->
     let ll =  range 0 (ES.cardinal (all_edges_ending_at in_n in_gr)) in
     List.fold_right (
         fun x igr ->
         add_edge in_n x out_n (out_p+x) tt1 igr) (List.rev ll) in_gr
  | _ ->
     add_edge in_n in_p out_n out_p tt1 in_gr

and add_each_in_list_to_node olis in_gr ex out_e ni appl =
  match ex with
  | [] -> (olis,in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ = (appl in_gr hde) in
     let in_gr_ = (add_edge_multiarity lasti pp out_e ni tt1 in_gr_) in
     add_each_in_list_to_node
       ((lasti,pp,tt1)::olis) in_gr_ tl out_e (ni+1) appl

and add_each_in_list_to_node_and_get_types olis in_gr ex out_e ni appl =
  match ex with
  | [] -> (olis,in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ = (appl in_gr hde) in
     let in_gr_ = (add_edge lasti pp out_e ni tt1 in_gr_) in
     add_each_in_list_to_node_and_get_types (tt1::olis)
       in_gr_ tl out_e (ni+1) appl

and get_types_from_graph g inc_blob =
  let g_ty_idx,g_tm,g_tmn =
    let {nmap=_;eset = _; symtab=_;
         typemap=tyblob;w=_} = g in tyblob in
  let inc_blob_ty_idx,inc_block_tm,inc_blob_tmn = inc_blob in

  let out_ty_idx =
    if (g_ty_idx >= inc_blob_ty_idx) then g_ty_idx else inc_blob_ty_idx in
  let merge_fn =
    fun k xo yo -> match xo,yo with
                   | Some x, Some y -> Some x
                   | None, yo -> yo
                   | xo, None -> xo in
  let out_tm =
    TM.merge merge_fn g_tm inc_block_tm in
  let out_tmn =
    MM.merge merge_fn g_tmn inc_blob_tmn in
  (out_ty_idx, out_tm, out_tmn)


and get_merged_typeblob_gr g1 g2 =
  let g_ty_idx,g_tm,g_tmn =
    let {nmap=_;eset = _; symtab=_;
         typemap=tyblob;w=_} = g1 in tyblob in
  let inc_blob_ty_idx,inc_block_tm,inc_blob_tmn =
    let {nmap=_;eset = _; symtab=_;
         typemap=tyblob;w=_} = g2 in tyblob in
  let out_ty_idx =
    if (g_ty_idx >= inc_blob_ty_idx) then g_ty_idx else inc_blob_ty_idx in
  let merge_fn =
    fun k xo yo -> match xo,yo with
                   | Some x, Some y -> Some x
                   | None, yo -> yo
                   | xo, None -> xo in
  let out_tm =
    TM.merge merge_fn g_tm inc_block_tm in
  let out_tmn =
    MM.merge merge_fn g_tmn inc_blob_tmn in
  (out_ty_idx, out_tm, out_tmn)

and merge_typeblobs tyblob1 tyblob2 =
  let g_ty_idx,g_tm,g_tmn = tyblob1 in
  let inc_blob_ty_idx,inc_block_tm,inc_blob_tmn = tyblob2 in
  let out_ty_idx =
    if (g_ty_idx >= inc_blob_ty_idx) then g_ty_idx else inc_blob_ty_idx in
  let merge_fn =
    fun k xo yo -> match xo,yo with
                   | Some x, Some y ->
                      Some x
                   | None, yo -> yo
                   | xo, None -> xo in
  let out_tm =
    TM.merge merge_fn g_tm inc_block_tm in
  let out_tmn =
    MM.merge merge_fn g_tmn inc_blob_tmn in
  (out_ty_idx, out_tm, out_tmn)

and add_type_to_typemap ood
{nmap = nm;eset=pe;symtab=sm;typemap =(id,tm,tmn);w=pi} =
  match ood with
  | Basic BOOLEAN ->
     ((1,0,1),{nmap = nm;eset = pe;symtab = sm;
        typemap = (id,TM.add 1 ood tm, MM.add "BOOLEAN" 1 tmn); w = pi})
  | Basic CHARACTER ->
     ((2,0,2),{nmap = nm;eset = pe;symtab = sm;
        typemap = (id,TM.add 2 ood tm, MM.add "CHARACTER" 2 tmn); w = pi})
  | Basic REAL ->
     ((3,0,3),{nmap = nm; eset = pe;symtab = sm;
        typemap = (id,TM.add 3 ood tm, MM.add "REAL" 3 tmn);w = pi})
  | Basic DOUBLE ->
     ((4,0,4),{nmap = nm;eset = pe;symtab = sm;
        typemap = (id,TM.add 4 ood tm, MM.add "DOUBLE" 4 tmn);w = pi})
  | Basic INTEGRAL ->
     ((5,0,5),{nmap = nm;eset = pe;symtab = sm;
        typemap = (id,TM.add 5 ood tm, MM.add "INTEGRAL" 5 tmn);w = pi})
  | Basic NULL ->
     ((6,0,6),{nmap = nm;eset = pe;symtab = sm;
        typemap = (id,TM.add 6 ood tm, MM.add "NULL" 6 tmn);w = pi})
  | _ ->
     ((id,0,id),{nmap = nm;eset = pe;symtab = sm;
                 typemap = (id+1,TM.add id ood tm, tmn);w = pi})

and map_exp in_gr in_explist expl appl =
  match in_explist with
  | [] -> (expl,in_gr)
  | hde::tl ->
     let (lasti,pp,tt),in_gr = (appl in_gr hde) in
     map_exp in_gr tl (expl@[(lasti,pp,tt)]) appl

and add_a_tag (namen,tagty,ss) ((id,p,q),in_gr) =
  let (tt_id,ii,_),in_gr = add_sisal_type in_gr tagty in
  add_type_to_typemap (Union (tt_id,id,namen)) in_gr

and add_a_field (namen,tag_ty,ss) ((id,p,q),in_gr) =
  let (tt_id,ii,_),in_gr = add_sisal_type in_gr tag_ty in
  add_type_to_typemap (Record (tt_id,id,namen)) in_gr

and add_a_tuple_entry tup_ty ((id,p,q),in_gr) =
  let (tt_id,ii,_),in_gr = add_sisal_type in_gr tup_ty in
  add_type_to_typemap (Tuple_ty (tt_id,id)) in_gr

and add_tag_spec (strlis,tl,_) in_gr =
  (strlis,tl,0),in_gr

and add_compound_type in_gr =
  function
  | Sisal_array s ->
     let (iii,iid,_), in_gr =
       add_sisal_type in_gr s in
     add_type_to_typemap (Array_ty iii) in_gr
  | Sisal_stream s ->
     let (iii,iid,_), in_gr =
       add_sisal_type in_gr s in
     add_type_to_typemap (Stream iii) in_gr
  | Sisal_union rrr ->
     let (tag_fst,ign,_),in_gr =
       List.fold_right
         (fun (tag_names_l,tag_ty) y ->
           List.fold_right
             add_a_tag
             (List.map (fun namen -> (namen,tag_ty,0)) tag_names_l) y)
         rrr
         ((0,0,0),in_gr) in
     add_type_to_typemap (Union (0,tag_fst,"")) in_gr
  | Sisal_record rrr ->
     let (rec_fst,ign,_),in_gr =
       List.fold_right
         (fun (rec_names_l,rec_ty) y ->
           List.fold_right
             add_a_field
             (List.map (fun namen -> (namen,rec_ty,0)) rec_names_l) y)
         rrr
         ((0,0,0),in_gr) in
     add_type_to_typemap (Record (0,rec_fst,"")) in_gr
  | Sisal_function_type (fn_name,tyargs,tyres) ->
     let (res_fst,_,_),in_gr =
       List.fold_right
         (fun curr_t out_stf ->
           add_a_tuple_entry curr_t out_stf) tyres ((0,0,0),in_gr) in
     let (arg_fst,_,_),in_gr =
       List.fold_right
         (fun curr_t out_stf ->
           add_a_tuple_entry curr_t out_stf) tyargs ((0,0,0),in_gr) in
     add_type_to_typemap (Function_ty (arg_fst,res_fst,fn_name)) in_gr
  | _ ->
     raise (Node_not_found "In compound type")

and lookup_ty ij in_gr =
  let { nmap = nm; eset = pe; symtab = sm; typemap = (id,tm,tmn); w = pi; } =  in_gr in
  try
    TM.find ij tm
  with _ ->
    (Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);
    print_endline ("When looking up " ^ (string_of_int ij));
    raise (Sem_error "Error looking up type"))

and find_ty_safe
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} aty =
  let lookin_vals =
    try
      TM.fold (fun ke va z ->
          if aty = va then raise (Val_is_found ke) else z) tm 0
    with Val_is_found ke -> ke in
  if lookin_vals = 0 then
    raise
      (Node_not_found
         ("Type not found by find_ty in typemap: " ^
           (string_of_if1_ty aty)))
  else lookin_vals

and find_ty
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} aty =
  let lookin_vals =
    try
      TM.fold (fun ke va z ->
          if aty = va then raise (Val_is_found ke) else z) tm 0
    with Val_is_found ke -> ke in
  if lookin_vals = 0 then
    raise
      (Node_not_found
         (let _ = outs_graph {
                      nmap = nm;
                      eset = pe;
                      symtab = sm;
                      typemap = (id,tm,tmn);
                      w = pi;
                    }; in
          "Type not found byf ind_ty in typemap: " ^ (string_of_if1_ty aty)))
  else lookin_vals

and add_sisal_typename
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} namen ty_id =
  (ty_id,
   {
     nmap = nm;
     eset=pe;
     symtab = sm;
     typemap = (id,tm,MM.add namen ty_id tmn);
     w=pi;
  })

and lookup_by_typename
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);

  w = pi;
} namen =
  try
    MM.find namen tmn
  with _ ->
    raise (Node_not_found "not finding a type in typemap")

and add_sisal_type {nmap = nm;eset = pe;symtab = sm;
                    typemap = (id,tm,tmn);  w = pi;} aty =
  let in_gr = {nmap = nm;eset = pe;symtab = sm;
               typemap = (id,tm,tmn); w = pi;} in
  match aty with
  | Boolean -> add_type_to_typemap (Basic BOOLEAN) in_gr
  | Character -> add_type_to_typemap (Basic CHARACTER) in_gr
  | Double_real -> add_type_to_typemap (Basic DOUBLE) in_gr
  | Integer -> add_type_to_typemap (Basic INTEGRAL) in_gr
  | Null -> add_type_to_typemap (Basic NULL) in_gr
  | Real -> add_type_to_typemap (Basic REAL) in_gr
  | Compound_type ct ->
     add_compound_type {nmap = nm;eset = pe;
                        symtab = sm;typemap = (id,tm,tmn);
                        w = pi;} ct
  | Ast.Type_name ty ->
     match MM.mem ty tmn with
     | true -> (MM.find ty tmn, 0, MM.find ty tmn), in_gr
     | false ->
        let brr = string_of_graph in_gr in
          raise
          (Printexc.print_raw_backtrace stdout
             (Printexc.get_callstack 150);
           (Node_not_found ("typename being looked up:" ^ ty)));
(** Combine symtabs to initialize a new graph. **)
and get_a_new_graph in_gr =
  let in_gr = get_symtab_for_new_scope in_gr in
  let {nmap=nm;eset=ne;symtab=(_,ps);
       typemap=tmmi;w=tail} = in_gr in
  let {nmap=nm;eset=ne;symtab=_;
       typemap=tmn1;w=tail} =
    get_empty_graph tmmi in
  let tmn1 = merge_typeblobs tmn1 tmmi in
  let out_gr = {nmap=nm;eset=ne;symtab=(SM.empty,ps);
   typemap=tmn1;w=tail} in
  out_gr

and num_to_node_sym = function
  |	0	->	   BOUNDARY
  |	1	->	   CONSTANT
  |	2	->	   GRAPH
  |	3	->	   OLD
  |	4	->	   VAL
  |	5	->	   INVOCATION
  |	6	->	   NOT
  |	7	->	   NEGATE
  |	8	->	   ACATENATE
  |	9	->	   AND
  |	10	->	   DIVIDE
  |	11	->	   TIMES
  |	12	->	   SUBTRACT
  |	13	->	   ADD
  |	14	->	   OR
  |	15	->	   NOT_EQUAL
  |	16	->	   EQUAL
  |	17	->	   LESSER_EQUAL
  |	18	->	   LESSER
  |	19	->	   GREATER_EQUAL
  |	20	->	   GREATER
  |	21	->	   RBUILD
  |	22	->	   RELEMENTS
  |	23	->	   RREPLACE
  |	24	->	   SBUILD
  |	25	->	   SAPPEND
  |	26	->	   TAGCASE
  |	27	->	   SELECT
  |	28	->	   RANGEGEN
  |	29	->	   AADDH
  |	30	->	   AADDL
  |	31	->	   ABUILD
  |	32	->	   AELEMENT
  |	33	->	   AFILL
  |	34	->	   AGATHER
  |	35	->	   AISEMPTY
  |	36	->	   ALIML
  |	37	->	   ALIMH
  |	38	->	   AREPLACE
  |	39	->	   AREML
  |	40	->	   AREMH
  |	41	->	   ASCATTER
  |	42	->	   ASETL
  |	43	->	   ASIZE
  |	44	->	   INTERNAL
  |	45	->	   REDUCE
  |	46	->	   REDUCELEFT
  |	47	->	   REDUCERIGHT
  |	48	->	   REDUCETREE
  |	49	->	   STREAM
  |	50	->	   FINALVALUE
  |	51	->	   MULTIARITY
  | _ -> raise (Sem_error  "Error looking up type")

and node_sym_to_num = function
  | BOUNDARY	->	0
  | CONSTANT	->	1
  | GRAPH	->	2
  | OLD	        ->	3
  | VAL	        ->	4
  | INVOCATION	->	5
  | NOT	        ->	6
  | NEGATE	->	7
  | ACATENATE	->	8
  | AND	        ->	9
  | DIVIDE	->	10
  | TIMES	->	11
  | SUBTRACT	->	12
  | ADD	        ->	13
  | OR	        ->	14
  | NOT_EQUAL	->	15
  | EQUAL	->	16
  | LESSER_EQUAL ->	17
  | LESSER	 ->	18
  | GREATER_EQUAL ->	19
  | GREATER	->	20
  | RBUILD	->	21
  | RELEMENTS	->	22
  | RREPLACE	->	23
  | SBUILD	->	24
  | SAPPEND	->	25
  | TAGCASE	->	26
  | SELECT	->	27
  | RANGEGEN	->	28
  | AADDH	->	29
  | AADDL	->	30
  | ABUILD	->	31
  | AELEMENT	->	32
  | AFILL	->	33
  | AGATHER	->	34
  | AISEMPTY	->	35
  | ALIML	->	36
  | ALIMH	->	37
  | AREPLACE	->	38
  | AREML	->	39
  | AREMH	->	40
  | ASCATTER	->	41
  | ASETL	->	42
  | ASIZE	->	43
  | INTERNAL	->	44
  | REDUCE	->	45
  | REDUCELEFT	->	46
  | REDUCERIGHT	->	47
  | REDUCETREE	->	48
  | STREAM	->	49
  | FINALVALUE	->	50
  | MULTIARITY	->	51

and string_of_node_sym = function
  | BOUNDARY     -> "BOUNDARY"
  | CONSTANT     -> "CONSTANT"
  | GRAPH        -> "GRAPH"
  | OLD          -> "OLD"
  | VAL          -> "VAL"
  | INVOCATION   -> "INVOCATION"
  | NOT          -> "NOT"
  | NEGATE       -> "NEGATE"
  | ACATENATE     -> "ACATENATE"
  | AND          -> "AND"
  | DIVIDE       -> "DIVIDE"
  | TIMES        -> "TIMES"
  | SUBTRACT     -> "SUBTRACT"
  | ADD          -> "ADD"
  | OR           -> "OR"
  | NOT_EQUAL    -> "NOT_EQUAL"
  | EQUAL        -> "EQUAL"
  | LESSER_EQUAL -> "LESSER_EQUAL"
  | LESSER       -> "LESSER"
  | GREATER_EQUAL-> "GREATER_EQUAL"
  | GREATER      -> "GREATER"
  | AELEMENT     -> "AELEMENT"
  | ABUILD       -> "ABUILD"
  | AFILL        -> "AFILL"
  | AREPLACE     -> "AREPLACE"
  | RBUILD       -> "RBUILD"
  | RELEMENTS    -> "RELEMENTS"
  | RREPLACE     -> "RREPLACE"
  | SBUILD       -> "SBUILD"
  | SAPPEND      -> "SAPPEND"
  | TAGCASE      -> "TAGCASE"
  | SELECT       -> "SELECT"
  | RANGEGEN     -> "RANGEGEN"
  | ASCATTER     -> "ASCATTER"
  | ASIZE        -> "ASIZE"
  | AADDH        -> "AADDH"
  | AADDL        -> "AADDL"
  | ASETL        -> "ASETL"
  | ALIML        -> "ALIML"
  | ALIMH        -> "ALIMH"
  | AREMH        -> "AREMH"
  | AREML        -> "AREML"
  | AISEMPTY     -> "AISEMPTY"
  | INTERNAL     -> ""
  | AGATHER      -> "AGATHER"
  | REDUCE       -> "REDUCE"
  | REDUCELEFT   -> "REDUCELEFT"
  | REDUCERIGHT  -> "REDUCERIGHT"
  | REDUCETREE   -> "REDUCETREE"
  | STREAM       -> "STREAM"
  | FINALVALUE   -> "FINALVALUE"
  | MULTIARITY   -> "MULTIARITY"

and string_of_pragmas p =
  List.fold_right
    (fun p q ->
      let l =
	match p with
	| Bounds ( i, j) ->
	   "Bounds (" ^ (string_of_int i) ^ "," ^ (string_of_int j) ^ ")"
	| SrcLine ( i,j) ->
	   "SrcLine (" ^ (string_of_int i) ^ "," ^ (string_of_int j) ^ ")"
	| OpNum i ->
	   "OpNum " ^ (string_of_int i)
	| Ar i ->
	   "Ar " ^ (string_of_int i)
	| Of i ->
	   "Of " ^ (string_of_int i)
	| Lazy ->
	   "Lazy"
	| Name str ->
	   "%na=" ^ str
	| Ref ->
	   "Ref"
	| Pointer ->
	   "Pointer"
	| Contiguous ->
	   "Contiguous"
	| None ->
	   "" in (cate_nicer l q " ,")) p ""

and string_of_if1_ty ity = match ity with
  | Array_ty a ->
     "ARRAY " ^ (string_of_int a)
  | Basic bc ->
     string_of_if1_basic_ty bc
  | Function_ty (if1l,if2l,fn_name) ->
     "FUNCTION_TYPE " ^ fn_name ^ " (ARGS: " ^ (string_of_int if1l) ^
       ") (RETURNS:" ^ (string_of_int if2l) ^ ")"
  | Multiple bc ->
     "Multiple " ^ (string_of_if1_basic_ty bc)
  | Record (fty,nfty, namen) ->
     "RECORD {" ^
       (cate_list
          ["Type label:" ^ (string_of_int fty);
           "Next field:" ^ (string_of_int nfty);
           "%na=" ^ namen
          ] "; ") ^ "}"
  | Stream bc ->
     "STREAM (" ^ (string_of_int bc) ^ ")"
  | Tuple_ty (fty,nty) ->
     "TUPLE {"  ^
       (cate_list
          ["Type label:" ^ (string_of_int fty);
           "Next label:" ^ (string_of_int nty);
          ] "; ") ^ "}"
  | Union (lab1,lab2,namen) ->
     "UNION {" ^
       (cate_list
          ["Type label:" ^ (string_of_int lab1);
           "Next tag:" ^ (string_of_int lab2);
           "%na="^namen] "; ") ^ "}"
  | Unknown_ty -> ""
  | Field if1li ->
     "Fields " ^
       List.fold_right
	 (fun x y -> (string_of_int x) ^ "; " ^ y)
         if1li ""
  | Tag if1li ->
     "Tags " ^
       List.fold_right
	 (fun x y -> (string_of_int x) ^ "; " ^ y)
         if1li ""
  | If1Type_name tt ->
     "TYPENAME " ^ (string_of_int tt)

and string_of_if1_basic_ty bc =
  match bc with
  | BOOLEAN   -> "BOOLEAN"
  | CHARACTER -> "CHARACTER"
  | DOUBLE    -> "DOUBLE"
  | INTEGRAL  -> "INTEGRAL"
  | NULL      -> "NULL"
  | REAL      -> "REAL"
  | UNION     -> "UNION"
  | STREAM    -> "STREAM"
  | ARRAY     -> "ARRAY"
  | RECORD    -> "RECORD"

and string_of_ports pa =
  "[|" ^ (Array.fold_right
	    (fun x y -> cate_nicer x y ",") pa "") ^ "|]"
and string_of_pair_list zz =
  ("[" ^ (List.fold_right (fun (x,y) z ->
              cate_nicer (("("^(string_of_int x))
                          ^ "," ^ ((string_of_int y) ^ ")"))
                z ";") zz "") ^ "]")

and string_of_pair_list_final_string zz =
  ("[" ^ (List.fold_right (fun (x,y,w) z ->
              cate_nicer (("("^(string_of_int x))
                          ^ "," ^ ((string_of_int y) ^
                                     "," ^ w ^ ")"))
                z ";") zz "") ^ "]")

and string_of_node_ty ?(offset=2) =
  fun n ->
  match n with
  | Literal (lab,ty,str,pout) ->
     (string_of_int lab) (*^ " " ^ (string_of_if1_basic_ty ty)*)
     ^ " \"" ^ str  ^ "\"" (*^ (string_of_ports pout)*)
  | Simple (lab,n,pin,pout,prag) ->
     cate_nicer
       (cate_nicer
          (cate_nicer
             (cate_nicer
                (string_of_int lab)
                (string_of_node_sym n) " ")
             (string_of_ports pin) " ")
          (string_of_ports pout) " ")
       (string_of_pragmas prag) " "
  | Compound (lab,sy,ty,pl,g,assoc) ->
     cate_nicer
       (cate_nicer
          (cate_nicer
             (cate_nicer
                ((string_of_int lab) ^ " " ^ (string_of_int ty))
                (string_of_pragmas pl) " ")
             (string_of_graph ~offset:(offset+2) g)
             "\n")
          (string_of_node_sym sy)
          " ")
       (List.fold_right
          (fun x y -> cate_nicer (string_of_int x) y ",")
        assoc "")
     " "
  | Unknown_node -> "Unknown"
  | Boundary (zz,yy,pp) ->
     let bb =
       (cate_nicer
          (cate_nicer
             (string_of_pair_list_final_string zz)
             (string_of_pair_list yy)
             ", ")
          (string_of_pragmas pp) ", ")
     in "BOUNDARY [" ^ bb ^ "]"

and string_of_node n_int g =
  string_of_node_ty (get_node n_int g)

and string_of_edge ((n1,p1),(n2,p2),tt) =
  cate_nicer
    ((string_of_int n1) ^ ":" ^ (string_of_int p1) ^ " -> "
     ^ (string_of_int n2) ^ ":" ^ (string_of_int p2))
    (string_of_int tt) " "

and string_of_edge_set ne =
  let ee =
    (ES.fold
       (fun x y -> (string_of_edge x)::y)
       ne [])
  in match ee with
     | [] -> []
     | _ ->"----EDGES----"::ee

and dot_of_node_ty id in_gr =
  fun n ->
  match n with
  | Literal (lab,ty,str,pout) ->
     (string_of_int id) ^ (string_of_int lab) ^
       " [shape=plaintext;label=\"" ^ str  ^ "\"]"
  | Simple (lab,n,pin,pout,prag) ->
     (string_of_int id) ^ (string_of_int lab) ^
       " [shape=rect;label=\""^
       (string_of_int lab)^ " "  ^
         (cate_nicer (string_of_node_sym n)
            (string_of_pragmas prag) ":") ^ "\"]"
  | Compound (lab,sy,ty_lab,pl,g,assoc) ->
     "subgraph cluster_"^ (string_of_int id) ^ (string_of_int lab) ^
       " {\n" ^"label=\"" ^ (string_of_int lab) ^ " "
       ^ (string_of_pragmas pl) ^ "\";\n" ^
         (dot_of_graph (int_of_string
                          ((string_of_int id) ^ (string_of_int lab)))
            g) ^ "\n" ^ "}"
  | Unknown_node -> "Unknown"
  | Boundary (zz,yy,pp) ->
     "IN0" ^ (string_of_int id) ^ " [shape=rect;label=\"" ^
       (cate_list (string_of_symtab_gr_in in_gr) "\\n") ^ "\"];\n" ^
         "OUT0" ^  (string_of_int id) ^
           " [shape=rect;label=\"" ^
             (cate_list (string_of_symtab_gr_out in_gr) "\\n") ^
               (string_of_pair_list yy) ^ (string_of_pragmas pp) ^ "\"]"

and graph_clean_multiarity in_gr =
  cleanup_multiarity in_gr

and dot_of_node_map id mn in_gr =
  NM.fold
     (fun k v z ->
       (cate_nicer z (dot_of_node_ty id in_gr v) ";\n")) mn ""

and dot_of_edge id ((n1,p1),(n2,p2),tt) =
  let process_n1 id =
    function 0 -> "IN0" ^ (string_of_int id)
           | n1 -> (string_of_int id) ^ (string_of_int n1) in
  let process_n2 id =
    function 0 -> "OUT0" ^ (string_of_int id)
           | n2 -> (string_of_int id) ^ (string_of_int n2) in
  (process_n1 id n1) ^ " ->  " ^ (process_n2 id n2) ^
     " [label=\"(" ^
       (string_of_int p1) ^ "," ^
         (string_of_int p2) ^ "),Ty=" ^
           (string_of_int tt) ^ "\"]"

and dot_of_edge_set id ne =
  ES.fold
    (fun x y -> cate_nicer y (dot_of_edge id x) "\n")
    ne ""

and dot_of_graph id in_gr =
let
  {nmap=nm;eset=ne;symtab=sm;typemap=(t,tm,tmn);w=tail} = in_gr in
cate_nicer
  (dot_of_node_map id nm in_gr) (dot_of_edge_set id ne) "\n"

and write_dot_file in_gr =
  let oc = open_out "out.dot" in
  fprintf oc "%s"
    ("digraph R {\nnewrank=true;\n" ^ ( dot_of_graph 0 in_gr) ^ "}");
  close_out oc;
  "Output Dot in out.dot"

and dot_graph in_gr =
  let na,oc = Filename.open_temp_file "graph-" ".dot" in
  fprintf oc "%s"
    ("digraph R {\nnewrank=true;\n" ^ ( dot_of_graph 0 in_gr) ^ "}");
  close_out oc;

  print_endline  ( "Output Dot in " ^ na); ""

and write_any_dot_file sss in_gr =
  let oc = open_out sss in
  fprintf oc
    "%s" ("digraph R {\nnewrank=true;\n" ^ ( dot_of_graph 0 in_gr) ^ "}");
  close_out oc;
  "Output Dot in"

and string_of_node_map ?(offset=2) mn =
  let nn =
    (NM.fold
       (fun k v z ->
         ((string_of_node_ty ~offset:(offset) v)::z)) mn [])
  in match nn with
     | [] -> []
     | _ ->"----NODES----"::nn

and string_of_if1_value tm = function
  | {val_ty=ii;val_name=st;val_def=jj;def_port=p} ->
     let ttt =
       match (TM.mem ii tm)
       with | true -> string_of_if1_ty (TM.find ii tm)
            | false -> "" in
     ttt ^ ";" ^
       st ^ ";" ^ "(" ^ (string_of_int jj) ^
         "," ^ (string_of_int p) ^ ")"

and string_of_if1_value_in tm = function
  | {val_ty=ii;val_name=st;val_def=jj;def_port=p} ->
     let ttt =
       match (TM.mem ii tm)
       with | true -> string_of_if1_ty (TM.find ii tm)
            | false -> "" in
     if jj = 0 then
       ttt ^ ";" ^
         st ^ ";" ^ "(" ^ (string_of_int jj) ^
           "," ^ (string_of_int p) ^ ")"
     else ""

and string_of_if1_value_out tm = function
  | {val_ty=ii;val_name=st;val_def=jj;def_port=p} ->
     let ttt =
       match (TM.mem ii tm)
       with | true -> string_of_if1_ty (TM.find ii tm)
            | false -> "" in
     if jj != 0 then
       "{" ^ ttt ^ ";" ^
         st ^ ";" ^ "(" ^ (string_of_int jj) ^
           "," ^ (string_of_int p) ^ ")}"
     else ""

and string_of_symtab (ls, gs) tm =
  let ls =
    (SM.fold
       (fun k v z -> ((string_of_if1_value tm v)::z)) ls []) in
  let ls =
    match ls with
    | [] -> []
    | _ -> "LOCAL-SYM: "::ls in
  let gs = SM.fold
             (fun k v z ->
               ((string_of_if1_value tm v):: z)) gs [] in
  let gs =
    match gs with
    | [] -> []
    | _ -> "GLOBAL-SYM: ":: gs in gs@ls

and string_of_symtab_gr in_gr =
  let
    {nmap=nm;eset=ne;symtab=(ls,gs);typemap=(t,tm,tmn);w=tail} = in_gr in
  (SM.fold
     (fun k v z -> ((string_of_if1_value tm v)::z)) ls [])

and string_of_symtab_gr_in in_gr =
  let
    {nmap=nm;eset=ne;symtab=(ls,gs);typemap=(t,tm,tmn);w=tail} = in_gr in
  (SM.fold
     (fun k v z -> ((string_of_if1_value_in tm v)::z)) ls [])

and string_of_symtab_gr_out in_gr =
  let
    {nmap=nm;eset=ne;symtab=(ls,gs);typemap=(t,tm,tmn);w=tail} = in_gr in
  (SM.fold
     (fun k v z -> ((string_of_if1_value_out tm v)::z)) ls [])

and string_of_typenames tmn =
  let tmn =
    MM.fold
      (fun k v z ->
        (k ^ ":" ^ (string_of_int v))::z) tmn [] in
  match tmn with
  | [] -> []
  | _ -> "----TYPENAMES----"::tmn

and string_of_typemap tm =
  let tm = TM.fold (fun k v z ->
               ((string_of_int k ) ^
                  " " ^ (string_of_if1_ty v))::z) tm [] in
  match tm with
  | [] -> []
  | _ -> "----TYPEMAP----"::tm

and string_of_tyblob (x,y,z) =
  cate_list_pad 0
    (("ty_num:" ^ (string_of_int x))::
       (string_of_typemap y) @ (string_of_typenames z)) "\n"

and string_of_triple_int (i,j,k) =
  ("(" ^ (string_of_int i) ^
         "," ^ (string_of_int j) ^
           "," ^ (string_of_int k) ^
             ")")

and string_of_triple_int_list zz =
  List.fold_left (fun zz (i,j,k) -> zz ^ (string_of_triple_int (i,j,k))) "" zz

and string_of_graph ?(offset=0)
{nmap=nm;eset=ne;symtab=sm;typemap=(t,tm,tmn);w=tail} =
  cate_list_pad offset
    ("Graph {"::
       (string_of_node_map ~offset:(offset) nm)
     @ (string_of_edge_set ne)
     @ (string_of_symtab sm tm)
     @ (if offset = 0 then
          ((string_of_typemap tm)
           @ (string_of_typenames tmn))
        else [])
     @ ["} " ^ (string_of_int tail)]) "\n"

and string_of_graph2 (ii,gr) = string_of_graph gr

and graph_printer fmt gr =
  Format.fprintf fmt "-------\n%s\n" (string_of_graph gr)

and int_map_printer fmt inmap =
  Format.fprintf fmt "-------\n%s\n"
    ((IntMap.fold (
          fun ke valu old ->
          (string_of_int ke) ^ " : " ^ (string_of_int valu) ^ "\n" ^ old))
       inmap "")
and outs_graph gr =
  graph_printer Format.std_formatter gr
and outs_graph_with_msg msg gr =
  print_endline msg;
  outs_graph gr
and node_printer fmt ii in_gr =
  Format.fprintf fmt "------\n%s\n" (string_of_node ii in_gr)

and outs_node ii gr =
  node_printer Format.std_formatter ii gr

and nmap_printer fmt nm =
  Format.fprintf fmt "------\n%s\n"
    (cate_list (string_of_node_map nm) "\n")

and outs_nmap
  {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} =
  nmap_printer Format.std_formatter nm

and symtab_printer fmt (cs,ps,tm) =
  Format.fprintf fmt "----------\n%s\n" (cate_list (string_of_symtab (cs,ps) tm) "\n")

and outs_syms {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} =
  symtab_printer Format.std_formatter (cs,ps,tm)

let bind_name nam (n,p,ty) in_gr =
  match in_gr with
    {nmap=nm;eset=es;symtab = (cs,ps);typemap=tmm;w = i} ->
    {nmap=nm;eset=es;
     symtab =
       (SM.add nam {val_ty=ty;val_name=nam;
                    val_def=n;def_port=p} cs,ps);
     typemap=tmm;w=i}

let get_symbol_id v in_gr =
  match in_gr with
    {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} ->
    if (SM.mem v cs = true) then
      let {val_ty=t; val_name=_; val_def=aa; def_port=p} =
        SM.find v cs in
      (aa,p,t),in_gr
    else
      if (SM.mem v ps = true) then (
        let {val_ty=t;val_name=vv_n;
             val_def=aa;def_port=p} =
          SM.find v ps in
        let ap = boundary_in_port_count in_gr in
        let cs = SM.add v {val_ty=t;val_name=vv_n;
                           val_def=0;def_port=ap} cs in
        let in_gr = {nmap=nm;eset=es;symtab=(cs,ps);
                     typemap=ii,tm,tmn;w=i} in
        let {val_ty=t; val_name=_;
             val_def=aa; def_port=p} =
          SM.find v cs in
        (aa,ap,t),add_to_boundary_inputs ~namen:v 0 ap in_gr
      ) else (
        print_endline v;
        outs_syms in_gr;
        raise (Printexc.print_raw_backtrace stdout
                 (Printexc.get_callstack 150);
               Node_not_found ( "Symbol lookup failed for name: " ^ v));
      )

let get_symbol_id_old v in_gr =
  match in_gr with
    {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} ->
     if (SM.mem ("OLD " ^ v) cs = true) then
       let {val_ty=t; val_name=_; val_def=aa; def_port=p} =
         SM.find v cs in
       (aa,p,t),in_gr
     else if (SM.mem v cs = true) then
       let {val_ty=t; val_name=vv; val_def=aa; def_port=p} =
         SM.find v cs in
       let cs = SM.add ("OLD " ^ vv)
                  {val_ty=t; val_name=("OLD " ^ vv);
                   val_def=aa; def_port=p} cs in
       (aa,p,t),{nmap=nm;eset=es;symtab=(cs,ps);typemap=ii,tm,tmn;
                 w=i}
     else if (SM.mem ("OLD " ^ v) ps = true) then
       let {val_ty=t; val_name=_; val_def=aa; def_port=p} =
         SM.find v ps in
       (aa,p,t),in_gr
     else if (SM.mem v ps = true) then
       let {val_ty=t; val_name=vv; val_def=aa; def_port=p} =
         SM.find v ps in
       let ps = SM.add ("OLD " ^ vv)
                  {val_ty=t; val_name=("OLD " ^ vv);
                   val_def=aa; def_port=p} ps in
       (aa,p,t),{nmap=nm;eset=es;symtab=(cs,ps);typemap=ii,tm,tmn;
                 w=i}
     else
       raise (Node_not_found (
                  "Symbol not found in current or parent symtab: OLD " ^ v))

let is_outer_var vv = function
    {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} ->
    SM.mem vv ps
