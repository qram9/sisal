open Ast
open Format
open Printf
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
  | INTERNAL
  | AGATHER
  | REDUCE
  | STREAM
  | FINALVALUE

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
  | Array of label
  | Basic of basic_code
  | Function of label list * label list
  | Multiple of basic_code
  | Record of label * label * string
  | Stream of label
  | Tuple of label list
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
  | Compound of N.t * node_sym * pragmas * graph * N.t list
  | Literal of N.t * basic_code * string * ports
  | Boundary of (label * int) list * (label * int) list * pragmas
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
  | Compound (x,_,_,_,_) -> x
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
  {nmap = nm;eset = es;
   symtab = (other_cs,
             let kkk = fun k v z -> SM.add k v z in
             (SM.fold kkk cs (SM.fold kkk ps other_ps)));
   typemap = tm;w = i}

and copy_cs_syms_to_cs
{nmap=_;eset=es;symtab=(cs,ps);typemap=_;w=_}
{nmap=nm;eset=es;symtab=(other_cs,other_ps);typemap=tm;w=i} =
  let {nmap = nm;eset = es;
       symtab = (cs,ps); typemap = tm;w = i} =
    {nmap = nm;eset = es;
     symtab =
       (let kkk =
          fun k {val_name=vn_n;
                 val_ty=t1;val_def=_;def_port=_}
              (z,cou) ->
          if SM.mem k other_ps = false then
            (print_endline ("adding:"^ (vn_n));
             ((SM.add k
              {val_name=vn_n;
               val_ty=t1;val_def=0;
               def_port=cou} z),cou+1))
          else (z,cou) in
        let other_cs,_ =
          SM.fold kkk cs (other_cs,SM.cardinal other_cs) in
        other_cs,other_ps);
     typemap = tm;w = i} in
  let rec make_a_small_lis x y alis =
    if x < y then
      make_a_small_lis (x+1) y ((0,x)::alis)
    else alis in
  let boun_lis = make_a_small_lis 0 (SM.cardinal cs) [] in
  let in_gr =  {nmap = nm;eset = es;
                symtab = (cs,ps); typemap = tm;w = i} in
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

and add_to_boundary_outputs srcn srcp in_gr =
  match get_boundary_node in_gr with
  | (Boundary (in_port_list,out_port_list,boundary_p)) ->
     let {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} = in_gr in
     let annod = NM.find srcn nm in
     let annod =
       (match annod with
        | Simple (lab,n,pin,pont,prag) ->
           let mylis = Array.to_list pont in
           let mylis = (string_of_int 0)::mylis in
           Simple (lab,n,pin,(Array.of_list mylis),prag)
        | _ -> annod) in
     (add_edge2 srcn srcp 0 (List.length out_port_list) 0
        {nmap=NM.add 0
                (Boundary (in_port_list,(srcn,srcp)::out_port_list,boundary_p))
                (NM.add srcn annod nm);
         eset=es;symtab=sm;typemap=tm;w=pi})
  | _ -> in_gr

and add_to_boundary_inputs n p in_gr =
  match get_boundary_node in_gr with
  | (Boundary (in_port_list,out_port_list,boundary_p)) ->
     if List.mem (n,p) in_port_list then
       in_gr
     else
       (let {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} = in_gr in
        {nmap=NM.add 0
                (Boundary ((n,p)::in_port_list,out_port_list,boundary_p))
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

and output_to_boundary alis in_gr =
     match alis with
      | (srcn,srcp)::tl ->
         output_to_boundary tl (add_to_boundary_outputs srcn srcp in_gr)
      | [] -> in_gr

and input_from_boundary alis in_gr =
     match alis with
      | (srcn,srcp)::tl ->
         input_from_boundary tl (add_to_boundary_inputs srcn srcp in_gr)
      | [] -> in_gr

and set_out_port_str src_nod src_port dest_nn =
  match src_nod with
  | Literal (lab,ty,str,pout) ->
     Literal (lab,ty,str,(pout.(src_port) <- (pout.(src_port)) ^ dest_nn;pout))
  | Simple (lab,n,pin,pout,prag) ->
     Simple (lab,n,pin,(pout.(src_port) <- (pout.(src_port)) ^ dest_nn;pout),prag)
  | Compound (lab, sy, pl, g, assoc) ->
     (*let boundary_node = set_out_port (get_node 0 g) src_port dest_nn in
       Compound (lab,sy,pl,update_node 0 boundary_node g, assoc)*)
     src_nod
  | Boundary (_,_,p) -> src_nod
  | Rajathi -> src_nod

and set_in_port dst_nod dst_port src_nn =
  match dst_nod with
  | Literal (lab,ty,str,pout) ->
     dst_nod
  | Simple (lab,n,pin,pout,prag) ->
     if pin.(dst_port) != "" then
       raise (Node_not_found "in_port set already")
     else
       Simple (lab,n,(pin.(dst_port) <- string_of_int src_nn;pin),pout,prag)
  | Compound (lab, sy, pl, g, assoc) -> (*
     let boundary_node = set_in_port (get_node 0 g) dst_port src_nn in
     Compound (lab, sy, pl,update_node 0 boundary_node g, assoc)*)
     dst_nod
  | Boundary _ -> dst_nod
  | Rajathi -> dst_nod

and set_in_port_str dst_nod dst_port src_str =
  match dst_nod with
  | Literal (lab,ty,str,pout) ->
     dst_nod
  | Simple (lab,n,pin,pout,prag) ->
     Simple (lab,n,(pin.(dst_port) <-  src_str;pin),pout,prag)
  | Compound (lab,sy, pl, g, assoc) -> (*
     let boundary_node = set_in_port (get_node 0 g) dst_port src_nn in
     Compound (lab,sy,pl,update_node 0 boundary_node g, assoc)*)
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
         Simple (lab,n,(pin.(dst_port) <- "Literal:" ^ str_;pin),pout,prag)
      | Compound (lab, sy,pl, g, assoc) ->
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
  | `Compound (g,sy,prag,alis) ->
     {nmap = NM.add pi (Compound(pi,sy,prag,g,alis)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
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

and add_node_2 nn
{nmap = nm;eset = pe;symtab = sm;typemap = tm;w = pi} =
  match nn with
  | `Simple (n,pin,pout,prag) ->
     (pi,0,0),
     {nmap =
        NM.add pi
	  (Simple(pi,n,pin,pout,prag)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
  | `Compound (g,sy,prag,alis) ->
     (pi,0,0),
     {nmap =
        NM.add pi
	  (Compound(pi,sy,prag,g,alis)) nm;
      eset = pe;symtab = sm;typemap = tm;w = pi+1}
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

and add_edge n1 p1 n2 p2 ed_ty in_gr =
  Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);
  let ii =
  if n1 = 0 && n2 = 0 then
    (print_endline ("Trying to connect:" ^
                     (string_of_edge ((n1,p1),(n2,p2),ed_ty))); "ii")
  else "k" in
  let in_gr =
    (if n1 = 0 then add_to_boundary_inputs 0 p1 in_gr else in_gr) in
  let in_gr =
    (if n2 = 0 then add_to_boundary_outputs n2 p2 in_gr else in_gr) in
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let anod1 = NM.find n1 nm in
  let anod2 = NM.find n2 nm in
  (*match anod1 with
    |     Literal (lab,ty,str,pout) ->
       (l et anod2 = set_in_port_str anod2 p2 ("\"" ^ str ^ "\"") in
        le   t nm = NM.add n2 anod2 nm in
        {nmap   = nm;eset = pe;symtab = sm;typemap = tm;w = pi;})
    | _ ->*)
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
   { nmap = nm;
     eset = ES.add ((n1,p1),(n2,p2),ed_ty) pe;
     symtab = sm;typemap = tm;w = pi;})

and add_each_in_list in_gr ex lasti appl =
  match ex with
  | [] -> ((lasti,0,0),in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ = (appl in_gr hde) in
     add_each_in_list in_gr_ tl lasti appl

and add_each_in_list_to_node olis in_gr ex out_e ni appl =
  match ex with
  | [] -> (olis,in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ = (appl in_gr hde) in
     let in_gr_ = (add_edge lasti pp out_e ni tt1 in_gr_) in
     add_each_in_list_to_node
       ((lasti,pp)::olis) in_gr_ tl out_e (ni+1) appl


and add_each_in_list_to_node_and_get_types olis in_gr ex out_e ni appl =
  match ex with
  | [] -> (olis,in_gr)
  | hde::tl ->
     let (lasti,pp,tt1),in_gr_ = (appl in_gr hde) in
     let in_gr_ = (add_edge lasti pp out_e ni tt1 in_gr_) in
     add_each_in_list_to_node_and_get_types (tt1::olis) in_gr_ tl out_e (ni+1) appl

and add_type_to_typemap ood
{nmap = nm;eset=pe;symtab=sm;typemap =(id,tm,tmn);w=pi} =
  match ood with
  | Basic BOOLEAN ->
     ((1,0,1),{nmap = nm;eset = pe;symtab = sm;
        typemap = (id,TM.add 1 ood tm, MM.add "BOOLEAN" 1 tmn);w = pi})
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
     let (lasti,pp,_),in_gr = (appl in_gr hde) in
     map_exp in_gr tl (expl@[(lasti,pp,0)]) appl

and add_a_tag (namen,tagty,ss) ((id,p,q),in_gr) =
  let (tt_id,ii,_),in_gr = add_sisal_type in_gr tagty in
  add_type_to_typemap (Union (tt_id,id,namen)) in_gr

and add_a_field (namen,tag_ty,ss) ((id,p,q),in_gr) =
  let (tt_id,ii,_),in_gr = add_sisal_type in_gr tag_ty in
  add_type_to_typemap (Record (tt_id,id,namen)) in_gr

and add_tag_spec (strlis,tl,_) in_gr =
  (strlis,tl,0),in_gr

and add_compound_type in_gr =
  function
  | Sisal_array s ->
     let (iii,iid,_), in_gr =
       add_sisal_type in_gr s
     in add_type_to_typemap (Array iii) in_gr
  | Sisal_stream s ->
     let (iii,iid,_), in_gr =
       add_sisal_type in_gr s
     in add_type_to_typemap (Stream iii) in_gr
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
  | _ ->
     raise (Node_not_found "In compound type")

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
                    typemap = (id,tm,tmn); w = pi;} aty =
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
  | INTERNAL     -> ""
  | AGATHER      -> "AGATHER"
  | REDUCE       -> "REDUCE"
  | STREAM       -> "STREAM"
  | FINALVALUE   -> "FINALVALUE"

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
  |  Array a ->
      "ARRAY " ^ (string_of_int a)
  | Basic bc ->
     string_of_if1_basic_ty bc
  | Function (if1l,if2l) ->
     "Function (ins: " ^
       (List.fold_right
	  (fun x y ->
	    (string_of_int x) ^ "," ^ y)
	  if1l "")
       ^ ") (outs:" ^
	 (List.fold_right
	    (fun x y -> (string_of_int x) ^ "," ^ y)
	    if2l "") ^ ")"
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
     "Stream (" ^ (string_of_int bc) ^ ")"
  | Tuple if1l ->
     "Tuple "  ^
       (List.fold_right
	  (fun x y -> (string_of_int x) ^ ";" ^ y)
	  if1l "") ^ ")"
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
  | Compound (lab,sy,pl, g, assoc) ->
     cate_nicer
       (cate_nicer
          (cate_nicer
             (cate_nicer
                (string_of_int lab)
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
             (string_of_pair_list zz)
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
  | Compound (lab,sy,pl,g,assoc) ->
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
     "{" ^ ttt ^ ";" ^
       st ^ ";" ^ "(" ^ (string_of_int jj) ^
         "," ^ (string_of_int p) ^ ")}"

and string_of_if1_value_in tm = function
  | {val_ty=ii;val_name=st;val_def=jj;def_port=p} ->
     let ttt =
       match (TM.mem ii tm)
       with | true -> string_of_if1_ty (TM.find ii tm)
            | false -> "" in
     if jj = 0 then
       "{" ^ ttt ^ ";" ^
         st ^ ";" ^ "(" ^ (string_of_int jj) ^
           "," ^ (string_of_int p) ^ ")}"
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
    | _ -> "}"::"{"::"LOCAL-SYM: "::ls in
  let gs = SM.fold
             (fun k v z ->
               ((string_of_if1_value tm v):: z)) gs [] in
  let gs =
    match gs with
    | [] -> []
    | _ -> "{"::"GLOBAL-SYM: ":: gs in gs@ls@["}"]

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

and outs_node n gr =
  Format.fprintf Format.std_formatter  "-------\n%s\n" (string_of_node n gr)

let get_symbol_id v in_gr = match in_gr with
    {nmap=nm;eset=es;symtab=(cs,ps);typemap = ii,tm,tmn;w = i} ->
    if (SM.mem v cs = true) then
      let {val_ty=t; val_name=_; val_def=aa; def_port=p} =
        SM.find v cs in
      (aa,p,t),in_gr
    else
      if (SM.mem v ps = true) then (
        let {val_ty=t;val_name=vv_n;val_def=aa;def_port=p} =
          SM.find v ps in
        print_endline ("Found in PS:" ^ vv_n);
        let ap = boundary_in_port_count in_gr in
        let cs = SM.add v {val_ty=t;val_name=vv_n;val_def=0;def_port=ap} cs in
        let in_gr = {nmap=nm;eset=es;symtab=(cs,ps);typemap=ii,tm,tmn;w=i} in
        let {val_ty=t; val_name=_; val_def=aa; def_port=p} =
          SM.find v cs in
        (aa,ap,t),add_to_boundary_inputs 0 ap in_gr
      ) else (
        print_endline v;
        raise (Node_not_found "got a problem here");
      )
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
