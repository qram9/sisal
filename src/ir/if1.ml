open Ast
open Format
open Printf

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
  | CONSTANT
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
  | AELEMENT
  | ABUILD
  | AFILL
  | AREPLACE
  | RBUILD
  | RELEMENTS
  | RREPLACE
  | SBUILD
  | SAPPEND
  | TAGCASE
  | SELECT
  | RANGEGEN
  | ASCATTER
  | ASIZE
  | AADDH
  | AADDL
  | ALIML
  | ALIMH
  | AREMH
  | AREML
  | AISEMPTY
  | ASETL
  | INTERNAL
  | AGATHER
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

exception Sem_error of string
type ports = port array

let rec find_port an_array curr_idx len elem =
  if Array.get an_array curr_idx = elem
  then curr_idx
  else
    if curr_idx + 1 = len then
      raise (Node_not_found "in ports")
    else
      find_port an_array (curr_idx+1) len elem

type pragmas = pragma list

module N = struct
  type t = label
  let compare = Pervasives.compare
end

module T = struct
  type t = label
  let compare =
    Pervasives.compare
end

type port_idx = int

module E = struct
  type t = (N.t * port_idx) * (N.t * port_idx) * int
  (** Because no Fan-ins possible
      each edge gets to be unique **)
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

type graph =
  {
    nmap : node NM.t;
    eset : ES.t ;
    symtab : (if1_value SM.t * if1_value SM.t);
    typemap : int * if1_ty TM.t * int MM.t;
    w : int
  }

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
  | Rajathi

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
  | Rajathi -> 0

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
                   ("could not locate record:" ^
                      (string_of_int anum))))
   | false -> anum,0)

and get_graph_label
{nmap=_;eset=_;symtab=(_,_);typemap=_;w=i} = i

and get_graph_from_label ii
{nmap=nm;eset=_;symtab=(_,_);typemap=_;w=_} = match NM.find ii nm with
  | Compound (_,_,_,_,gg,_) -> gg
  | _ -> raise (Sem_error "Lookup failed for compound")

and has_node i
{nmap=nm;eset =_;symtab=(_,_);typemap=_;w=_} = NM.mem i nm

and get_node i
{nmap=nm;eset=_;symtab=(_,_);typemap=_;w=_} = NM.find i nm

and unify_syms
{nmap=nm;eset=es;symtab=(cs,ps);typemap=tm;w=i} =
  {nmap=nm;eset=es;
   symtab=(SM.empty,SM.fold (fun k v z -> SM.add k v z) cs ps);
   typemap=tm;w=i}

and update_parent_syms
{nmap=_;eset=_;symtab=(cs,ps);typemap=_;w=_}
{nmap=nm;eset=es;symtab=(other_cs,other_ps);typemap=tm;w=i} =
  (** Union ps, other_ps With curr
      And Make It A New Parent Symtab *)
  {nmap=nm;eset=es;
   symtab=(other_cs,
           let kkk = fun k v z -> SM.add k v z in
           (SM.fold kkk cs (SM.fold kkk ps other_ps)));
   typemap=tm;w=i}

and redirect_incoming_for_symbol
{nmap=nm;eset=es;symtab=(cs,ps);typemap=tm;w=w} n1 p1 =
  let new_cs =
    let get_k_v =
      SM.filter (
          fun k {val_name=nn;
                 val_ty=t1; val_def=ni;
                 def_port=np} ->
          ni = n1 && np = p1) cs in
    let kkk = fun k v z -> SM.add k v z in
    SM.fold kkk cs get_k_v in
  {nmap=nm;eset=es;symtab=(new_cs,ps);typemap=tm;w=w}

and copy_cs_syms_to_cs
{nmap=_;eset=es;symtab=(cs,ps);typemap=_;w=_}
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
                typemap = tm;w = i} in
  let in_gr = input_from_boundary boun_lis in_gr in
  in_gr

and update_node n_int nnode in_gr =
  match in_gr with
    {nmap=nm;
     eset=pe;
     symtab=sm;
     typemap=tm;
     w=pi
    } ->
    { nmap=NM.add n_int nnode nm;
      eset=pe;symtab=sm;typemap=tm;w=pi}

and get_boundary_node {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} =
  NM.find 0 nm

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
         output_to_boundary tl
           (add_to_boundary_outputs ~start_port:start_port srcn srcp tyy in_gr)
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
  | Rajathi -> src_nod

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
  | Rajathi -> dst_nod

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
  | Rajathi -> dst_nod

and set_in_port_str dst_nod dst_port src_str =
  match dst_nod with
  | Literal (lab,ty,str,pout) ->
     dst_nod
  | Simple (lab,n,pin,pout,prag) ->
     Simple (lab,n,safe_set_arr src_str dst_port pin,pout,prag)
  | Compound (lab,sy,ty, pl, g, assoc) ->
     dst_nod
  | Boundary _ -> dst_nod
  | Rajathi -> dst_nod

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
      | Rajathi -> dst_nod)
  | _ -> dst_nod

and add_node nn
{nmap = nm;eset = pe;symtab = sm;typemap = tm;w = pi} =
  match nn with
  | `Simple (n,pin,pout,prag) ->
     {nmap = NM.add pi (Simple(pi,n,pin,pout,prag)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
  | `Compound (g,sy,ty,prag,alis) ->
     {nmap = NM.add pi (Compound(pi,sy,ty,prag,g,alis)) nm;
      eset = pe;symtab = sm;typemap = get_tymap g ;w = pi+1}
  | `Literal (ty_lab,str,pout) ->
     {nmap = NM.add pi (Literal(pi,ty_lab,str,pout)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
  | `Boundary ->
     {nmap = NM.add 0 (Boundary([],[],[])) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi;}

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

and get_tymap
{nmap = _;eset = _;symtab = _;typemap = (id,tm,tmn);w = _} =
  (id,tm,tmn)

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
     (pi,0,0),
     {nmap =
        NM.add pi
	  (Compound(pi,sy,ty,prag,g,alis)) nm;
      eset = pe;symtab = sm;typemap = get_tymap g;w = pi+1}
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
        (Format.printf "Ending:%d\n" yp;
        IntMap.add yp y_ty acc) else acc) pe res in
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
  let es = ES.filter (fun ((x,xp),(y,yp),y_ty) -> NM.mem x nm) es in
  let nm = NM.fold (fun k v zz ->
               NM.add k (clear_port_str v) zz) nm NM.empty in
  let in_gr = {nmap = nm;eset=es;symtab=sm;typemap=tm;w=pi} in
  let {nmap = nm;eset=es;symtab=sm;typemap=tm;w=pi} =
    ES.fold (fun x z_gr -> add_from_edge x z_gr) es in_gr in
  let nm,multiar_nodes =
    NM.fold
      (fun k v (z,edges) ->
        match v with
        | Simple(_,MULTIARITY,_,_,_) ->
           if (ES.cardinal (all_edges_ending_at k in_gr)) = 0 then
             z,k::edges
           else
             NM.add k v z,edges
        | Compound(lab,sy,ty,pl,g,assoc) ->
           NM.add k (
               Compound (lab,sy,ty,pl,
                         (cleanup_multiarity g),assoc)) z, edges
        | _ -> NM.add k v z,edges)
      nm (NM.empty,[]) in
  let es = List.fold_left
             (fun ese x ->
               ES.diff ese (all_edges_ending_at x in_gr))
             es multiar_nodes in
  {nmap = nm;eset=es;symtab=sm;typemap=tm;w=pi}

and remove_edge n1 p1 n2 p2 ed_ty in_gr =
  Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);
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
    let (x,y),(u,v),ty = List.hd edges in
    (x,y,ty)

and add_edge n1 p1 n2 p2 ed_ty in_gr =
  Printexc.print_raw_backtrace stdout (Printexc.get_callstack 2);
  let n1,p1,ed_ty = match get_node n1 in_gr with
    | Simple (_,MULTIARITY,_,_,_) ->
       let n1,p1,ed_ty =
         node_incoming_at_port n1 p1 in_gr in
       (n1,p1,ed_ty)
    | _ -> n1,p1,ed_ty in
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

     let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
     let anod1 = NM.find n1 nm in
     let anod2 = NM.find n2 nm in
     (let anod1 =
        if n1 != 0 then
          set_out_port_str anod1 p1
            ("(" ^ (string_of_int n2) ^ "," ^ (string_of_int p2) ^ ")")
        else anod1 in
      let anod2 =
        if n2 != 0 then
          set_in_port_str anod2 p2
            ("(" ^ (string_of_int n1) ^ "," ^ (string_of_int p1) ^ ")")
        else anod2 in
      let nm = NM.add n1 anod1 nm in
      let nm = NM.add n2 anod2 nm in
      let in_gr = add_edge2 n1 p1 n2 p2 ed_ty in_gr in
      in_gr))

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
  print_endline ("multiarity edges:" ^
                   (cate_list (string_of_edge_set edges) ";"));
  print_endline ("Ending at:" ^
                   (cate_list (string_of_edge_set
                                 (all_edges_ending_at n1 in_gr)) ";"));
  let ending_at = (all_edges_ending_at n1 in_gr) in
  let redir_set,_ = redirect_edges n2
                    (ES.diff ending_at edges) in
  let { nmap = nm;
        eset = es;
        symtab = sm;typemap = tm;w = pi;} = in_gr in
  let es = ES.union
             redir_set in
  let  { nmap = nm; eset = es;
         symtab = sm;typemap = tm;w = pi;} =
    ES.fold (
        fun ((x,xp),(y,yp),yt) gr ->
        add_edge x xp y yp yt gr) redir_set in_gr in
  let es = (ES.diff (ES.diff es ending_at) edges) in
  let in_gr =  { nmap = nm; eset = es;
                 symtab = sm;typemap = tm;w = pi;} in
  in_gr

and add_each_in_list in_gr ex lasti appl =
  match ex with
  | [] -> ((lasti,0,0),in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ = (appl in_gr hde) in
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
         (fun (Field_spec(rec_names_l,rec_ty)) y ->
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

and lookup_ty ij
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} = TM.find ij tm

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
          "Type not found by find_ty in typemap: " ^ (string_of_if1_ty aty)))
  else lookin_vals

and get_ret_ty_list
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} funty =
  try
    let funv = TM.find funty tm in
    (match funv with
     | Function_ty (arg_ty, ret_ty, anma) ->
        let rec fold_to_lis aty tm =
          if aty = 0 then []
          else
            (let this_ty =
               TM.find aty tm in
             match this_ty with
             | Tuple_ty(aty,nty)-> aty::(fold_to_lis nty tm)
             | _ -> raise (Sem_error (
                               "Unknown function type:" ^
                                 (string_of_int funty)))) in
        fold_to_lis ret_ty tm
     | _ ->
        raise (Sem_error ("Unknown function type:" ^ (string_of_int funty))))
  with Not_found ->
    raise (Sem_error ("Unknown function type:" ^ (string_of_int funty)))

and find_fun_ty
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} fn_name =
  let lookin_vals =
    try
      TM.fold (fun ke va z ->
          match va with
          |  Function_ty (_,_,anam) ->
              (if anam = fn_name then raise (Val_is_found ke) else z)
          | _ -> z) tm 0
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
          "FUNCTION Type not found by find_ty in typemap: " ^ fn_name))
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
     | true -> (MM.find ty tmn,0, MM.find ty tmn), in_gr
     | false ->
        let brr = string_of_graph in_gr in
        print_endline brr;
        raise (Node_not_found ("typename being added:"^ty));

and get_a_new_graph in_gr =
  (** Combine symtabs to initialize
      a new graph. **)
  let in_gr = unify_syms in_gr in
  let {nmap=nm;eset=ne;symtab=(_,ps);
       typemap=tmmi;w=tail} = in_gr in
  let {nmap=nm;eset=ne;symtab=_;
       typemap=tmn1;w=tail} =
    get_empty_graph tmmi in
  {nmap=nm;eset=ne;symtab=(SM.empty,ps);
   typemap=tmn1;w=tail}

and string_of_node_sym = function
  | CONSTANT     -> "CONSTANT"
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
                ((string_of_int lab) ^ (string_of_int ty))
                (string_of_pragmas pl) " ")
             (string_of_graph ~offset:(offset+2) g)
             "\n")
          (string_of_node_sym sy)
          " ")
       (List.fold_right
          (fun x y -> cate_nicer (string_of_int x) y ",")
        assoc "")
     " "
  | Rajathi -> "Unknown"
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
       (string_of_node_sym n) ^ "\"]"
  | Compound (lab,sy,ty_lab,pl,g,assoc) ->
     "subgraph cluster_"^ (string_of_int id) ^ (string_of_int lab) ^
       " {\n" ^"label=\"" ^ (string_of_int lab) ^ " "
       ^ (string_of_pragmas pl) ^ "\";\n" ^
         (dot_of_graph (int_of_string
                          ((string_of_int id) ^ (string_of_int lab)))
            g) ^ "\n" ^ "}"
  | Rajathi -> "Unknown"
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
  fprintf oc "%s" ("digraph R {\nnewrank=true;\n" ^ ( dot_of_graph 0 in_gr) ^ "}");
  close_out oc;
  "Output Dot in out.dot"

and write_any_dot_file sss in_gr =
  let oc = open_out sss in
  fprintf oc "%s" ("digraph R {\nnewrank=true;\n" ^ ( dot_of_graph 0 in_gr) ^ "}");
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
  List.fold_left (fun zz (i,j,k) -> (string_of_triple_int (i,j,k)) ^ zz) "" zz

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

and outs_graph gr =
  graph_printer Format.std_formatter gr

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
        print_endline ("Found in PS:" ^ vv_n);
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
        raise (Node_not_found ( "Issue For Symbol: " ^ v));
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
     else
       raise (Node_not_found ("Issue For Symbol: OLD " ^ v))

let is_outer_var vv = function
    {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} ->
    SM.mem vv ps
   (** GRAPH is best to build inside out, due to the
    language strictness that we need a node and ports
    tuple
    AST visitor may build the GRAPH inside out
    TEST: we are able to look up nodes in IF1.NM
    with an integer
    TEST: Edges are pair of ints containing a
    label (integer) and another integer
    (which serves as an array-idx into a node's
    port.  Nodes are either
    | Simple of node-type (binary operators etc perhaps)
    and a port array)
    | Compound of a list of Graphs and port array
    Node numbers must be unique only inside Graphs to allow
    for import/export. Graphs boundaries have some special properties.
    There may require to be depth or breadth first visitors among other.
    There may require to be a node and adjacency list of incoming/outgoing edges,
    probably another array like the port arrays. **)
    (** Literal edge 5 tuple **)
    (** Literal of dest node, port, ref to type label, string, comment **)
    (** Edge:
    Literal edge
    type information
    comment section that has line number and or name **)
    (** Label Scoping: **)
    (** Type must also be stored in the Top-level graph **)
