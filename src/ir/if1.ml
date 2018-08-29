open Ast

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
  | MULTIPLY
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
  let compare =
    Pervasives.compare
end

module T = struct
  type t = label
  let compare =
    Pervasives.compare
end

type port_idx = int
module E = struct
  type t = (N.t * port_idx) * (N.t * port_idx) * if1_ty
  (** Because no Fan-ins possible each edge gets to be unique **)
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

let cate_nice a b =
  match b with
  |  "" -> a
  | _ ->
     match a with
     |  "" -> b
     | _ -> a ^ "," ^ b
          
let cate_nicer a b c =
  match b with
  |  "" -> a
  | _ ->
     match a with
     |  "" -> b
     | _ -> a ^ c ^ b

let rec cate_list a c =
  match a with
  |  hd::tl -> cate_nicer hd (cate_list tl c) c
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
  }
and node =
  | Simple of N.t * node_sym * ports * ports * pragmas
  | Compound of N.t * pragmas * graph * N.t list
  | Literal of N.t * basic_code * string * ports
  | Boundary of label list SM.t * (label * int) list * pragmas
  | Rajathi

let get_empty_graph =
  let nm = NM.add 0 (Boundary(SM.empty,[],[]))  NM.empty in
  {
    nmap = nm;
    eset = ES.empty;
    symtab = (SM.empty, SM.empty);
    typemap = (0, TM.empty, MM.empty);
    w = 1
  }

let rec get_node_label n =
  match n with
  | Simple (x, _, _, _,_) -> x
  | Compound (x, _,_,_) -> x
  | Literal (x,_,_,_) -> x
  | Boundary _ -> 0
  | Rajathi -> 0
  and
    get_graph_label
{
  nmap = _;
  eset = _;
  symtab = (_,_);
  typemap = _;
  w = i
} = i
  and has_node i
{
  nmap = nm;
  eset = _;
  symtab = (_,_);
  typemap = _;
  w = _
} =
    NM.mem i nm
  and get_node i
{
  nmap = nm;
  eset = _;
  symtab = (_,_);
  typemap = _;
  w = _
} =
    NM.find i nm
  and unify_syms
{
  nmap = nm;
  eset = es;
  symtab = (cs,ps);
  typemap = tm;
  w = i
} =
    {
      nmap = nm;
      eset = es;
      symtab = (SM.empty,
                SM.fold
                  (fun k v z ->
                    SM.add k v z) cs ps);
      typemap = tm;
      w = i
    }
  and update_node
n_int nnode in_gr =
    match in_gr with
      {nmap=nm;
       eset=pe;
       symtab=sm;
       typemap=tm;
       w=pi
      } ->
      {nmap=NM.add n_int nnode nm;
       eset=pe;
       symtab=sm;
       typemap=tm;
       w=pi}
  and update_boundary_link alis in_gr bb =
    match bb with
    | (Boundary (r,j,p)) ->
       (match alis with
        | (srcn,srcp)::tl ->
           let {nmap=nm;eset=es;symtab=sm;typemap=tm;w=pi} = in_gr in
           let annod = NM.find srcn nm in
           let annod =
             (match annod with
              | Simple (lab,n,pin,pont,prag) ->
                 let mylis = Array.to_list pont in
                 let mylis = (string_of_int 0)::mylis in
                 Simple (lab,n,pin,(Array.of_list mylis),prag)
              | _ -> annod) in
           update_boundary_link tl
             (add_edge2 srcn srcp 0 (List.length j) Unknown_ty
                {nmap=NM.add 0
                        (Boundary (r,(srcn,srcp)::j,p))
                        (NM.add srcn annod nm);
                 eset=es;symtab=sm;typemap=tm;w=pi})
             (Boundary (r,(srcn,srcp)::j,p))
        | [] -> in_gr)
    | _ -> in_gr
  and set_out_port_str src_nod src_port dest_nn =
    match src_nod with
    | Literal (lab,ty,str,pout) ->
       Literal (lab,ty,str,(pout.(src_port) <- (pout.(src_port)) ^ dest_nn;pout))
    | Simple (lab,n,pin,pout,prag) ->
       Simple (lab,n,pin,(pout.(src_port) <- (pout.(src_port)) ^ dest_nn;pout),prag)
    | Compound (lab, pl, g, assoc) ->(*
     let boundary_node = set_out_port (get_node 0 g) src_port dest_nn in
     Compound (lab,pl,update_node 0 boundary_node g, assoc)*)
       src_nod
    | Boundary (sym_map,ll,p) -> src_nod
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
    | Compound (lab, pl, g, assoc) -> (*
     let boundary_node = set_in_port (get_node 0 g) dst_port src_nn in
     Compound (lab,pl,update_node 0 boundary_node g, assoc)*)
       dst_nod
    | Boundary _ -> dst_nod
    | Rajathi -> dst_nod
  and set_in_port_str dst_nod dst_port src_str =
    match dst_nod with
    | Literal (lab,ty,str,pout) ->
       dst_nod
    | Simple (lab,n,pin,pout,prag) ->
       Simple (lab,n,(pin.(dst_port) <-  src_str;pin),pout,prag)
    | Compound (lab, pl, g, assoc) -> (*
     let boundary_node = set_in_port (get_node 0 g) dst_port src_nn in
     Compound (lab,pl,update_node 0 boundary_node g, assoc)*)
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
        | Compound (lab, pl, g, assoc) ->
           dst_nod
        | Boundary _ -> dst_nod
        | Rajathi -> dst_nod)
    | _ -> dst_nod
  and add_node nn
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = tm;
  w = pi
} =
    match nn with
    | `Simple (n,pin,pout,prag) ->
       {
         nmap = NM.add pi (Simple(pi,n,pin,pout,prag)) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;           
         w = pi+1
       }
    | `Compound (g,prag,alis) ->
       {
         nmap = NM.add pi (Compound(pi,prag,g,alis)) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;           
         w = pi+1
       }
    | `Literal (ty_lab,str,pout) ->
       {
         nmap = NM.add pi (Literal(pi,ty_lab,str,pout)) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;           
         w = pi+1
       }
    | `Boundary ->
       {
         nmap = NM.add 0 (Boundary(SM.empty,[],[])) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;
         w = pi;
       }
  and add_node_2 nn
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = tm;
  w = pi
} =
    match nn with
    | `Simple (n,pin,pout,prag) ->
       (pi,0),
       {
         nmap =
           NM.add pi
	     (Simple(pi,n,pin,pout,prag)) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;
         w = pi+1
       }
    | `Compound (g,prag,alis) ->
       (pi,0),
       {
         nmap =
           NM.add pi
	     (Compound(pi,prag,g,alis)) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;           
         w = pi+1
       }
    | `Literal (ty_lab,str,pout) ->
       (pi,0),
       {
         nmap =
           NM.add pi
             (Literal(pi,ty_lab,str,pout)) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;           
         w = pi+1
       }
    | `Boundary ->
       (pi,0),
       {
         nmap =
           NM.add 0 (Boundary(SM.empty,[],[])) nm;
         eset = pe;
         symtab = sm;
         typemap = tm;           
         w = pi+1
       }

  and add_edge2 n1 p1 n2 p2 ed_ty
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = tm;
  w = pi
} =
    {
      nmap = nm;
      eset = ES.add ((n1,p1),(n2,p2),ed_ty) pe;
      symtab = sm;
      typemap = tm;
      w = pi;
    }
    
  and add_edge n1 p1 n2 p2 ed_ty
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = tm;
  w = pi
} =
    let anod1 = NM.find n1 nm in
    let anod2 = NM.find n2 nm in  
    (*match anod1 with
    | Literal (lab,ty,str,pout) ->
       (let anod2 = set_in_port_str anod2 p2
                      ("\"" ^ str ^ "\"")  in
        let nm = NM.add n2 anod2 nm in
        {
          nmap = nm;
          eset = pe;
          symtab = sm;
          typemap = tm;
          w = pi;
       })               
    | _ ->*) 
       (let anod1 =
          if n1 != 0 then
            set_out_port_str anod1 p1
              ("(" ^ (string_of_int n2) ^ "," ^ (string_of_int p2) ^ ")")
          else
            anod1 in
        let anod2 =
          if n2 != 0 then    
            set_in_port_str anod2 p2
              ("(" ^ (string_of_int n1) ^ "," ^ (string_of_int p1) ^ ")")
          else anod2 in
        let nm = NM.add n1 anod1 nm in
        let nm = NM.add n2 anod2 nm in
        {
          nmap = nm;
          eset = ES.add ((n1,p1),(n2,p2),ed_ty) pe;
          symtab = sm;
          typemap = tm;
          w = pi;
       })

  and add_each_in_list in_gr ex lasti appl =
    match ex with
    | [] ->
       let iii = string_of_graph in_gr in
       ((lasti,0),in_gr)
    | hde::tl ->
       let (lasti,pp),in_gr_ = (appl in_gr hde) in
       let iii = string_of_graph in_gr_ in
       add_each_in_list in_gr_ tl lasti appl

  and mas ood {
nmap = nm;
eset = pe;
symtab = sm;
typemap = (id, tm, tmn);
w = pi
} =
    ((id,0),{
       nmap = nm;
       eset = pe;
       symtab = sm;
       typemap = (id+1,TM.add id ood tm, tmn);
       w = pi
    })
  and map_exp in_gr in_explist expl appl =
    match in_explist with
    | [] -> (expl,in_gr)
    | hde::tl ->
       let (lasti,pp),in_gr = (appl in_gr hde) in
       map_exp in_gr tl (expl@[(lasti,pp)]) appl
  and add_a_tag (namen,tag_ty) ((id,p),in_gr) =
    let (tt_id,ii),in_gr = add_sisal_type in_gr tag_ty in
    mas (Union (tt_id,id,namen)) in_gr
  and add_a_field (namen,tag_ty) ((id,p),in_gr) =
    let (tt_id,ii),in_gr = add_sisal_type in_gr tag_ty in
    mas (Record (tt_id,id,namen)) in_gr     
  and add_tag_spec (strlis,tl) in_gr =
    (strlis,tl),in_gr
  and add_compound_type in_gr =
    function
    | Sisal_array s ->
       let (iii,iid), in_gr =
         add_sisal_type in_gr s
       in mas (Array iii) in_gr
    | Sisal_stream s ->
       let (iii,iid), in_gr =     
         add_sisal_type in_gr s
       in mas (Stream iii) in_gr       
    | Sisal_union rrr ->
       let (tag_fst,ign),in_gr =
         List.fold_right
           (fun (tag_names_l,tag_ty) y ->
             List.fold_right
               add_a_tag
               (List.map (fun namen -> (namen,tag_ty)) tag_names_l) y)
           rrr
           ((0,0),in_gr) in
       mas (Union (0,tag_fst,"")) in_gr
    | Sisal_record rrr ->
       let (rec_fst,ign),in_gr =
         List.fold_right
           (fun (Field_spec(rec_names_l,rec_ty)) y ->
             List.fold_right
               add_a_field
               (List.map (fun namen -> (namen,rec_ty)) rec_names_l) y)
           rrr
           ((0,0),in_gr) in
       mas (Record (0,rec_fst,"")) in_gr
    | _ ->
       raise (Node_not_found "In compound type")
  and add_sisal_typename
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} namen =
    if MM.mem namen tmn = false then
      (id,
       {
         nmap = nm;
         eset=pe;
         symtab = sm;
         typemap = (id+1,tm,MM.add namen id tmn);
         w=pi;
      })
    else
      (MM.find namen tmn,
       {
         nmap = nm;
         eset = pe;
         symtab = sm;
         typemap = (id,tm,tmn);
         w = pi;
      })
  and add_sisal_type
{
  nmap = nm;
  eset = pe;
  symtab = sm;
  typemap = (id,tm,tmn);
  w = pi;
} aty =
    let in_gr = {
        nmap = nm;
        eset = pe;
        symtab = sm;
        typemap = (id,tm,tmn);
        w = pi;
      } in
    match aty with
    | Boolean ->
       mas (Basic BOOLEAN) in_gr
    | Character ->
       mas (Basic CHARACTER) in_gr
    | Double_real ->
       mas (Basic DOUBLE) in_gr
    | Integer ->
       mas (Basic INTEGRAL) in_gr
    | Null ->
       mas (Basic NULL) in_gr
    | Real ->
       mas (Basic REAL) in_gr
    | Compound_type ct ->
       add_compound_type
         {
           nmap = nm;
           eset = pe;
           symtab = sm;
           typemap = (id,tm,tmn);           
           w = pi;
         } ct
    | Ast.Type_name ty ->
       let ii,in_gr = add_sisal_typename in_gr ty in
       mas (If1Type_name ii) in_gr

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
    | MULTIPLY     -> "MULTIPLY"
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
	     "Name " ^ str
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
	      (fun x y -> cate_nice x y) pa "") ^ "|]"
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
    | Compound (lab, pl, g, assoc) ->
       cate_nicer
         (cate_nicer
            (cate_nicer
               (string_of_int lab)
               (string_of_pragmas pl) " ")
            (string_of_graph ~offset:(offset+2) g)
            "\n")
         (List.fold_right (fun x y -> cate_nice (string_of_int x) y)
            assoc " ")
         "\n"
    | Rajathi -> "Unknown"
    | Boundary (xx,yy,pp) ->
       let bb =
         (cate_nicer
            (cate_nicer
               (SM.fold (fun k v y -> cate_nicer k y ";") xx "")
               ("[" ^ (List.fold_right (fun (x,y) z ->
                           cate_nicer (("("^(string_of_int x))
                                       ^ "," ^ ((string_of_int y) ^ ")"))
                             z ";") yy "") ^ "]")
               ", ")
            (string_of_pragmas pp) ", ")
       in "BOUNDARY [" ^ bb ^ "]"
  and string_of_node n_int g =
    string_of_node_ty (get_node n_int g)
  and string_of_edge ((n1,p1),(n2,p2),tt) =
    cate_nicer
      ((string_of_int n1) ^ ":" ^ (string_of_int p1) ^ " -> "
       ^ (string_of_int n2) ^ ":" ^ (string_of_int p2))
      (string_of_if1_ty tt) " "
  and string_of_edge_set ne =
    let ee =
      (ES.fold
         (fun x y -> (string_of_edge x)::y)
         ne [])
    in match ee with
       | [] -> []
       | _ ->"----EDGES----"::ee
  and string_of_node_map ?(offset=2) mn =
    let nn =  
      (NM.fold
         (fun k v z ->
           ((string_of_node_ty ~offset:(offset) v)::z)) mn [])
    in match nn with
       | [] -> []
       | _ ->"----NODES----"::nn
  and string_of_if1_value tm = function
    | {val_ty=ii;val_name=str;val_def=jj} ->
       "{" ^ (string_of_if1_ty (TM.find ii tm)) ^ ";" ^
         str ^ ";" ^ (string_of_int jj) ^ "}"
  and string_of_symtab (ls, gs) tm =
    let ls = (SM.fold
                (fun k v z -> ((string_of_if1_value tm v)::z)) ls []) in
    let ls =
      match ls with
      | [] -> []
      | _ -> "--- LOCAL SYMTAB ---"::ls in
    let gs = SM.fold
               (fun k v z ->
                 ((string_of_if1_value tm v):: z)) gs [] in
    let gs =
      match gs with
      | [] -> []
      | _ -> "--- GLOBAL SYMTAB ---" :: gs in
    gs @ ls
  and string_of_typenames tmn =
    let tmn =
      MM.fold
        (fun k v z ->
          (k ^ ":" ^ (string_of_int v))::z) tmn [] in
    match tmn with
    | [] -> []
    | _ -> "----TYPENAMES----"::tmn
  and string_of_typemap tm =
    let tm =
      TM.fold
        (fun k v z ->
          ((string_of_int k ) ^ " " ^ (string_of_if1_ty v))::z) tm [] in
    match tm with
    | [] -> []
    | _ -> "----TYPEMAP----"::tm
  and string_of_graph ?(offset=0) {nmap=nm;eset=ne;symtab=sm;typemap=(t,tm,tmn);w=tail} =
    cate_list_pad offset
      ("Graph {"::(string_of_node_map ~offset:(offset) nm)
       @ (string_of_edge_set ne)
       @ (string_of_symtab sm tm)
       @ (string_of_typemap tm)
       @ (string_of_typenames tmn)
       @ ["} " ^ (string_of_int tail)]) "\n"
  and string_of_graph2 (ii,gr) =
    string_of_graph gr
let get_symbol_id v in_gr =
  match in_gr with
    {
      nmap = nm;
      eset = es;
      symtab = (cs,ps);
      typemap = ii,tm,tmn;
      w = i
    } ->
    if (SM.mem v cs = true) then
      let {val_ty = _; val_name = _; val_def = aa} =
        SM.find v cs
      in
      (aa,0),in_gr
    else
      if (SM.mem v ps = true) then
        let {val_ty = _; val_name = _; val_def = aa} =
          SM.find v ps in
        if aa = 0 then
          (if NM.mem 0 nm then
             (match NM.find 0 nm with
              | Boundary (smi,ll,pp) ->
                 (try
                    let k =
                      SM.find v smi
                    in
                    ((0,0),in_gr)
                  with _ ->
                    ((0,0),
                     {nmap = NM.add 0
                               (Boundary
                                  (SM.add v [0] smi,ll,pp)) nm;
                      eset = es;
                      symtab = (cs,ps);
                      typemap = ii,tm,tmn;
                      w = i;}
                    )
                 )
              | _ ->
                 raise (Node_not_found "Don't know how to handle this one"))
           else
             raise (Node_not_found "Node not found"))
        else
          (aa,0),in_gr
      else
        raise (Node_not_found "got a problem here");

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
