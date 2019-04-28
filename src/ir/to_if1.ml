(* TEST about multiple definition to same variable in a scope,
   add scope numbers, level etc. *)
(* Can we add array dope-vectors *)
(* TO_TEST: inputs to select do not seem to get from outer scope *)
(* TODO: forall do not seem to pull inputs from outside *)
(* many boundary boxes are empty *)

(** Ideas here mostly come from the single paper:
    "IF1, AN INTERMEDIATE FORM FOR APPLICATIVE LANGUAGES,
    JULY 31, 1985 VERSION 1.0".

    This is also useful:
    "FRONTEND OF A SISAL COMPILER, RIYAZ V.P,
    M.TECH THESIS INDIAN INST OF TECH. KANPUR, MARCH 1993". *)

(** IF1 is a dataflow graph format
    generated with some effort (boring and time consuming)
    using an AST visitor/walker for the applicative
    and single assignment SISAL langauge. The
    language has let bindings, compound statements
    like forall (perfect loops with scoping
    similar to nested lets, with mostly bindings
    similar to a standard let), for_initial,
    if expressions (select expressions), tagged unions
    which are mostly like ML variants but with one difference -
    sharing of the body expression by different tags is allowed,
    nested functions but no higher order functions
    (though, SISAL2 and SISAL90 supports higher order functions).
    Types would need to be provided by the user,
    for the most part, with an exception for arithmetic
    operations, for which the compiler infers types from the
    expression's operands. When types are specified, infered types
    need to be checked against the specified types etc.
    LET's are lowered here using hierarchical symtabs,
    with a parent symtab for enclosing-scope and
    one for current-scope.

    Each lowering function below may start with a do_, for example,
    do_exp, do_simple_exp etc. Their purpose would be to recursively
    lower an incoming AST type (for the two mentioned above, exp,
    simple_exp would be the AST type) to IF1. The return value
    is a quadruple, organized into a triplet of ints followed by
    a graph type: (x,y,z),gr. x signifying node-id,
    y for port-id and z for type-id all ints. gr is a graph type
    that you may find in if1.ml. The difficulty here is that
    we just return only one int for node-id. But AST types may return
    multiple values. So, what I did was introduce a MULTIARITY
    node, which adds each result from the AST type as
    incoming entries- When a node's result is connected with
    an user, the expectation is that we can propagate the input
    directly to the user, when the incoming node-type is
    MULTIARITY.

    A spate of library functions do exist and we do not support
    any yet...
    DOUBLE, TRIPLE are some shortcuts to create tuples from
    expressions or declarations.
    There are peculiarities in function declarations due to the need
    for forward declarations etc.

    What next:
    1: I also found reading Prof. Andrew Appel's book:
    "Compiling with Continuations" facinating--
    including callcc etc concepts.
    CPS callcc etc. Every compiler stage is discussed
    and also they discuss closure conversion etc.
    and maybe a CPS lowering would be fun to do...

    2: For better usability: SISAL2 etc had written about
    but not attempted...*)

open Ast
open If1

let in_port_1 =
  (** memory allocate arrays *)
  let in_array = Array.make 2 "" in
  in_array.(0) <- "0";
  in_array

let in_port_2 =
  let in_array = Array.make 2 "" in
  in_array.(0) <- "0";  in_array.(1) <- "1";
  in_array

let out_port_1 =
  let out_array = Array.make 2 "" in
  out_array.(0) <- "1";
  out_array

let in_port_0 = Array.make 0 ""
let out_port_0 = Array.make 0 ""

(** an expression like
   let x = 1 in sisal would
   need to return a constant
   and set x with that Node-id **)

(** Variable has a name and a type
   and has an associated expression **)

(**A LET EXP MAY CREATE A LOCAL SCOPE
   IN A FOLLOWING IN EXP, SO CURRENT
   SCOPE WOULD GET PUSHED IN.
   AFTER WE ARE OUT OF THE SCOPE,
   WE MUST NOT SEE THE ELEMENTS.**)

(** We have three numbers returned from
    each recursive call:-
    One for node#, one for port# and one for type#.*)

let rec zipem fst snd =
  (** Add a pair of elements to a list, from
      two input lists *)
  match fst, snd with
  | hd_fst::tl_fst, hd_snd::tl_snd ->
     (** function looks generic over any list
         but it is used so far when constructing from lets.
         Triple/Double are allowed here,
         maybe they should be scalarized **)
     (hd_fst,hd_snd)::(zipem tl_fst tl_snd)
  | _,_ ->[]

let rec string_of_zip zipped fst_fn snd_fn =
  match zipped with
  | (hd_fst, hd_snd)::tl_fst ->
     (*Triple/Double are allowed here*)
     "(" ^ (fst_fn hd_fst) ^ "," ^
       (snd_fn hd_snd) ^ ")" ^
         (string_of_zip tl_fst fst_fn snd_fn)
  | [] -> ""

let rec array_builder_exp ?(inc_typ=0) in_gr = function
    (** Helper function that code generates
        IF1 tree for building arrays *)
  | SExpr_pair(e,f) ->
     let (e,p,t1),in_gr = do_simple_exp in_gr e in
     (match f with
      | Empty ->
         (0,0,0),in_gr
      | Exp fe_lis ->
         let exp_l,in_gr =
           map_exp in_gr fe_lis [] do_simple_exp in
         let (arrnum,arrport,_),in_gr =
           add_node_2
             (`Simple (
                  ABUILD,
                  Array.make ((List.length fe_lis)+1) "",
                  Array.make 1 "" ,[None])) in_gr in
         let in_gr = add_edge e p arrnum 0 t1 in_gr in
         let in_gr = add_each_edge exp_l arrnum 1 in_gr in
         let t1 =
           if inc_typ = 0 then (
             try
               let aty =  Array_ty t1 in
               find_ty_safe in_gr aty
             with _ ->
               let aty =  Array_ty t1 in
               let _,in_gr = add_type_to_typemap aty in_gr in
               find_ty_safe in_gr aty)
           else inc_typ in
         (arrnum,arrport,t1),in_gr)

and add_each_edge edg_lis anode nn in_gr =
  (** Call add_edge for a list, connected
      to anode, starting at port nn*)
  (match edg_lis with
   | (edghd,edgp,tty)::edgtl ->
      add_each_edge edgtl anode (nn+1)
        (add_edge edghd edgp anode nn tty in_gr)
   | [] -> in_gr)

and add_edges_for_fields edg_lis anode nn in_gr =
  (** Minor variant of above function, add_each_edge *)
  (match edg_lis with
   | (ff,(edghd,edgp,tty))::edgtl ->
      add_edges_for_fields edgtl anode (nn+1)
        (add_edge edghd edgp anode nn tty in_gr)
   | [] -> in_gr)

and do_each_exp_in_strm in_gr = function
  (** Helper function for stream SAPPEND expression *)
  | (hdn,hdp,tt)::tll ->
     let (i,j,tt),in_gr = do_each_exp_in_strm in_gr tll in
     let (k,l,t1),in_gr = add_node_2
                            (`Simple
                               (SAPPEND,
                                Array.make 2 "",
                                Array.make 1"",
                                [None])) in_gr in
     (k,l,tt),(add_edge hdn hdp k 0 tt
                 (add_edge i j k 1 tt in_gr))

  | [] ->
     add_node_2 (`Simple
                   (SBUILD,
                    Array.make 1 "",
                    Array.make 1 "",[None])) in_gr

and get_tys ttts ous =
  (** Types are extracted from a
      triplet and added to a list *)
  match ttts with
  | (fn,(_,_,tt))::tl ->
     get_tys tl ((fn,tt)::ous)
  | [] -> ous

and union_builder in_gr utags iornone =
  (** Union or Record builder helper function *)
  let union_builder_impl in_gr = function
    | Tag_exp(tn,ex1) ->
       let exp_l,in_gr =
         do_simple_exp in_gr ex1 in
       (tn,exp_l),in_gr in
  let lll,in_gr = union_builder_impl in_gr utags in
  let {  nmap = nm;
         eset = pe;
         symtab = sm;
         typemap = (t,tm,tmn);
         w = pi
      } = in_gr in
  let tty = match lll with (fn,(_,_,tt)) -> (fn,tt) in
  let hdty =
    TM.fold
      (fun k v z ->
        (match z with
         |  Emp ->
             (let bar xx lt =
                (match xx,lt with
                 | hdf,hd -> Som k
                 | _ -> z) in
              match v with
              | Union (lt,_,xx) -> bar xx lt
              | _ -> z)
         | _ -> z)) tm Emp in
  let hdty =
    match hdty with
    | Som anum -> hdty
    | Emp -> raise (Node_not_found
                      "unknown field in an union") in
  let aout =
    (match iornone with
     | Emp ->
        (let eee = match hdty with
           | Som x -> x
           | _ -> 0 in
         match find_matching_record eee tm with
         | Som ii -> ii
         | _ -> 0)
     | Som ii -> ii) in
  let ff,(edghd,edgp,tty) = lll in
  let (bb,pp,t1),in_gr =
    add_node_2 (`Simple(
                    RBUILD,
                    Array.make 2 ff,
                    Array.make 1 "",[None])) in_gr in
  let in_gr = (add_edge edghd edgp bb t1 tty in_gr) in
  (bb,pp,aout),in_gr

and check_rec_ty tty_lis tm outlis =
  (** Do a type check recursively *)
  (** beef this up **)
  match tty_lis with
  | (hdf,hd)::tl ->
     let hdty =
       TM.fold
         (fun k v z ->
           (match z with
            |  Emp ->
                (let bar xx lt =
                   (match xx,lt with
                    | hdf,hd ->
                       Som k
                    | _ -> z) in
                 match v with
                 | Record (lt,_,xx) -> bar xx lt
                 | _ -> z)
            | _ -> z)) tm Emp in
     let hdt1y = match hdty with
       | Som anum -> anum
       | Emp -> raise (Node_not_found
                         "unknown field in a record") in
     check_rec_ty tl tm (hdty::outlis)
  | [] -> outlis

and find_matching_record eee tm =
  TM.fold (fun k v z ->
      (match z with
       |  Emp ->
           (match v with
            | Record (lt,nxt,xx) ->
               (match nxt = eee with
                | true -> Som k
                | false -> z)
            | _ -> z)
       | _ -> z)) tm Emp

and record_builder in_gr fdl iornone =
  (** TODO: SORT THIS OUT **)
  let rec record_builder_impl (aa,in_gr) = function
    | Field_def(Field_name fn,ex1)::tl ->
       let exp_l,in_gr =
         do_simple_exp in_gr ex1 in
       record_builder_impl ((fn,exp_l)::aa,in_gr) tl
    | [] -> aa,in_gr in(*field name must be matched *)
  let lll,in_gr =
    record_builder_impl ([],in_gr) fdl in
  let {  nmap = nm;
         eset = pe;
         symtab = sm;
         typemap = (t,tm,tmn);
         w = pi
      } = in_gr in
  let tty = get_tys lll [] in
  let aout = check_rec_ty tty tm [] in
  let aout =
    (match iornone with
     | Emp ->
        (let eee = match (List.hd aout) with
           | Som x -> x
           | _ -> 0 in
         match find_matching_record eee tm with
         | Som ii -> ii
         | _ -> 0)
     | Som ii -> ii) in
  let (bb,pp,t1),in_gr =
    add_node_2 (`Simple(
                    RBUILD,
                    Array.make ((List.length fdl)+1) "",
                    Array.make 1 "",[None])) in_gr in
  let in_gr = add_edges_for_fields lll bb t1 in_gr in
  (bb,pp,aout), in_gr

and add_edges_in_list exp_list anode portnum in_gr =
  (** Add edges from anode, starting at portnum and
      ending IF1 node tuple *)
  match exp_list with
  | (hd_node,in_port,tt)::tl ->
     add_edges_in_list
       tl
       anode
       (portnum+1)
       (add_edge hd_node in_port
          anode portnum tt in_gr)
  | [] -> ((anode,0,0),in_gr)

and do_iterator in_gr = function
  | Repeat dp ->
     do_decldef_part in_gr dp

and do_termination in_gr = function
  | While e ->
     do_exp in_gr e
  | Until e ->
     do_exp in_gr e

and do_constant in_gr xx =
  (** Return an IF1 node for
      constants *)
  let out_port_1 =
    let out_array = Array.make 1 "" in
    out_array in
  match xx with
  | False ->
     add_node_2 (
         `Literal
           (BOOLEAN,"False",out_port_1)) in_gr
  | Nil ->
     add_node_2 (
         `Literal
           (NULL,"Null",out_port_1)) in_gr
  | True ->
     add_node_2 (
         `Literal
           (BOOLEAN,"True",out_port_1)) in_gr
  | Int i ->
     add_node_2 (
         `Literal
           (INTEGRAL,(string_of_int i),out_port_1)) in_gr
  | Float f ->
     add_node_2 (
         `Literal
           (REAL,(string_of_float f),out_port_1)) in_gr
  | Char st ->
     add_node_2 (
         `Literal
           (CHARACTER,st,out_port_1)) in_gr
  | String st ->
     add_node_2 (
         `Literal
           (CHARACTER,st,out_port_1)) in_gr
  | Error st ->
     raise (
         Node_not_found
           "Error type- don't know what to do")

and do_val_internal in_gr v =
  (** 'v' may be a name of a variable or
      an 'old v' which may be used in
      for_initial bodies to keep copies
      from the previous iteration. *)
  match in_gr with
    {nmap=nmap;eset=eset;
     symtab=(umap,vma);typemap=oo,tm,tmn;w=w} ->
    let (nn,np,nty),in_gr =
      match v with
      |  `Std10 v ->
          print_endline ("Lowering val ref std " ^ (v));
                      get_symbol_id v in_gr
      | `OldMob v ->
          print_endline ("Lowering val ref old " ^ (v));
                      get_symbol_id_old v in_gr in
    let nn,np,nty = match get_node nn in_gr with
        (** If the defining node is MULTIARITY
            type, propagate its operand instead.
            Not recursive right now.*)
      | Simple (_,MULTIARITY,_,_,_) ->
         let nn,np,nty =
           node_incoming_at_port nn np in_gr in
         (nn,np,nty)
      | _ -> nn,np,nty in
    print_endline "Ref lowered to triple:";
    print_endline (string_of_triple_int (nn,np,nty));
    (nn,np,nty),in_gr

and do_val in_gr = function
  (** Look up the node defining a variable *)
  | Value_name v ->
     do_val_internal in_gr (`Std10 v)

and do_exp in_gr = function
  (** Add an expression using add_exp *)
  | Exp e ->
     add_exp in_gr e 0 []
  | Empty ->
     ((0,0,0), in_gr)

and extr_types in_gr = function
  (** Look up type of MULTIARITY *)
  | (xx,yy,zz),res ->
     let res,in_gr =
     let {nmap=nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
     let myn = NM.find xx nm in
     match myn with
     | Simple (lab,MULTIARITY,pl,g,assoc) ->
        let k =
          all_types_ending_at xx in_gr res in
        k,in_gr
     | _ ->
       let res = IntMap.add yy zz res in
       res,in_gr in
     print_endline ("Extracted types:");
     print_endline (IntMap.fold (fun x y z ->
                   (string_of_int x) ^ ":" ^ (string_of_int y) ^ z) res "");
     res,in_gr

and first_incoming_type_to_multiarity e in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter (fun ((x,xp),(y,yp),y_ty) -> y=e) pe in
  let _,_,t1 =
   try
   List.hd (ES.elements edges) with _ ->
     raise (Sem_error ("Error looking up first type in multiarity"))
  in t1

and first_incoming_triple_to_multiarity e in_gr =
  let {nmap = nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
  let edges = ES.filter (fun ((x,xp),(y,yp),y_ty) -> y=e) pe in
  let (x,xp),(y,yp),aty =
  try
   List.hd (ES.elements edges) with _ ->
   raise ((print_endline "Error with incoming triple lookup for graph:";
           print_endline (string_of_graph in_gr);
           Printexc.print_raw_backtrace stdout
           (Printexc.get_callstack 150));
          Sem_error ("Error looking up first triple in multiarity")) in
  (x,xp,aty)

and add_exp in_gr ex lasti ret_lis =
  (** Call do_simple_exp for each in list:ex and
      if there are multiple results, tie
      each result(s) to a MULTIARITY node in
      sequentially numbered input ports
      in the same order as list:ex. Some simple exp
      may provide MULTIARITY results-
      so handle those as well. If there is a single
      result, just return it without
      MULTIARITY. *)
  match ex with
  | [] ->
     if (List.length ret_lis) != 0
     then
       ((let in_port_1 =
           let in_array = Array.make (List.length ret_lis) "" in
           in_array in
         let out_port_1 =
           let out_array = Array.make (List.length ret_lis) "" in
           out_array in
         let (oo,op,ot),in_gr =
           add_node_2 (
               `Simple
                 (MULTIARITY, in_port_1, out_port_1,
		  [Name "LET"])) in_gr in
	 print_endline "Adding multiarity edges for an EXP list:";
         let {nmap = nm;eset = _;symtab = (_,_);
              typemap = _;w = _} = in_gr in
         let rec fold_away_multiarity_nodes alis oth_lis =
           (* Move CAR from alis to oth_lis, but only
              when CAR is non-MULTIARITY *)
           match alis with
           | (ahd,apo,aed_ty)::atl ->
              let new_alis,new_oth_lis =
                match NM.find ahd nm with
                | Simple(lab,MULTIARITY,_,_,_) ->
                   (all_nodes_joining_at (ahd,apo,aed_ty) in_gr)@atl,oth_lis
                | _ -> atl,(ahd,apo,aed_ty)::oth_lis in
              fold_away_multiarity_nodes new_alis new_oth_lis
           | [] -> alis,oth_lis in
         let _,ret_lis = fold_away_multiarity_nodes ret_lis [] in
         let rec add_all_edges_to_multiarity
                   (mo,mp,mt) in_gr = function
           | [] ->
              print_endline (string_of_node mo in_gr);
              (mo,mp,mt),in_gr
           | (hdn,hdp,hdt)::tl ->
              print_endline (string_of_node hdn in_gr);
              add_all_edges_to_multiarity
                (mo,mp+1,mt)
                (add_edge hdn hdp mo mp hdt in_gr)
                tl in
         let xyz,in_gr = add_all_edges_to_multiarity
                           (oo,op,ot) in_gr ret_lis in
         (oo,0,ot),in_gr))
     else
       ((0,0,0),in_gr)
  | hde::tl ->
     print_endline "Lowering exp with add_exp:";
     print_endline (str_simple_exp hde);
     let (lasti,pp,tt1),in_gr_ = do_simple_exp in_gr hde in
     add_exp in_gr_ tl lasti
       (ret_lis@[(lasti,pp,tt1)])

and do_exp_pair in_gr = function
  | Expr_pair (e,f) ->
     let (e,p,t1),in_gr =
       do_exp in_gr e in do_exp in_gr f

and do_field_name in_gr = function
  | Field_name f -> ((0,0,0), in_gr)

and do_field_exp in_gr = function
  | Field_exp (f,e) ->
     let f = do_field in_gr f in do_simple_exp in_gr e

and do_field in_gr = function
  | Ast.Field f ->
     add_each_in_list in_gr f 0 do_field_name

and do_field_def in_gr = function
  | Field_def (fn,ex) ->
     let fn = do_field_name in_gr fn in
     do_simple_exp in_gr ex

and do_in_exp ?(curr_level=1) in_gr = function
  (** Inexp
      1: Each expression in here must be of Arity two.
         The first and the second are the lower and upper bounds
         respectively, inclusive for the Index. For each number
         within these bounds, the index is defined to be that
         number, the definitions that depend on that
         index are made, and all the return expressions
         that depend on that index are evaluated. Each
         value in the range expression must be of type integer.
      2: Each expression in here must be of Arity one
         and of array type. In this case the shape of the array
         defines the range of execution of the for expression.
         If the array has one dimension, that dimension defines
         the range of execution. The body of the for executed once
         for each element of the array and during execution the
         identifier "value-name" is bound to the corresponding
         array element. If the array given is multi-dimensional and
         there is no "at" expression, the default range of
         the for expression is over the outermost dimension
         (that dimension that varies most slowly in a
         create-by-elements operation) of the array, since it
         must be defined as an array of arrays.
         Test#1: a range expression.
         Test#2: an array without "at". *)
  | In_exp (vn,e) ->
     let (aa,bb,cc),in_gr =
       (match e with
        | Exp ei ->
           (match ei with
            | [hd;tl] ->
               print_endline "Lowering forall to graph;in_exp type#1";
               (** Add each element in the exp to
                   a range generator graph.\n**)
               print_endline "Lowering range gen in_exp:";
               print_endline (str_simple_exp hd);
               print_endline (str_simple_exp tl);
               bin_fun hd tl in_gr RANGEGEN
            | [hd] ->
               print_endline "Lowering forall to graph; in_exp type#2";
               print_endline (string_of_graph in_gr);
               print_endline "Lowering only exp in in_exp:";
               print_endline (str_simple_exp hd);
               let (e,pi,t1),in_gr = do_simple_exp in_gr hd in
               let (scatter,_,_),in_gr =
                 get_simple_unary 2 in_gr ASCATTER in
               let t1 = (match (get_node e in_gr) with
               | Simple(la,MULTIARITY,_,_,_) ->
                 let t1 = first_incoming_type_to_multiarity e in_gr in t1
               | _ -> t1) in
               let outer_ty_num,inner_ty_num =
                 let rec walk_ty curr_ty curr_l =
                   let lookup_array_ty curr_ty in_gr =
                     match lookup_ty curr_ty in_gr with
                     | Array_ty ij ->
                         (curr_ty,ij)
                     | _ ->
                        raise (
                          Sem_error (
                              "Array type expected"^
                                " when constructing ASCATTER" ^
                                  (string_of_int curr_ty))) in
                   if curr_l = curr_level
                   then
                     (lookup_array_ty curr_ty in_gr)
                   else
                     (let outer_ty_num,inner_ty_num =
                        lookup_array_ty curr_ty in_gr in
                      walk_ty inner_ty_num (curr_l+1)) in
                 walk_ty t1 1 in
               let in_gr = add_edge e pi scatter 0 outer_ty_num in_gr in
               (scatter,0,inner_ty_num),in_gr
            | _ ->
               raise (Sem_error
                        ("Unsupported arity for in exp,"^
                           " must be 1 for array and 2 for"^
                             " comma separated bounds.\n")))
        | _ ->
           raise (Sem_error
                    ("Unsupported arity for in exp,"^
                       " must be 1 for array and 2 for"^
                         " comma separated bounds.\n"))) in
     let in_gr =
       match in_gr with
         {nmap=nmap;eset=eset;symtab=sm,pm;typemap=tm;w=w} ->
          match vn with
          | Value_name v ->
             {nmap=nmap;eset=eset;
              symtab=(SM.add v
                        {val_name=v;val_ty=cc;
                         val_def=aa;def_port=bb} sm,
                      pm);typemap=tm;w=w} in
     let in_gr = output_to_boundary
                   ~start_port:(boundary_in_port_count in_gr)
                   [(aa,bb,cc)] in_gr in
     (aa,bb,cc),in_gr

  | At_exp (ie,vns) ->
     (** The optional at clause is present in an in-exp.
         The value names following "at" denote index values of type
         integer corresponding to the current element value's
         position in the array. It is an error if the
         number of value names in the index list is greater than the
         number of dimensions of the array expression.
         The range of the for expression is the cross product
         over the number of ranges specified by the number of
         names in the index list. *)
     let (aa,bb,cc),in_gr =
       do_in_exp ~curr_level:curr_level in_gr ie in
     let in_gr =
       match in_gr with
         {nmap=nmap;eset=eset;symtab=sm,pm;typemap=tm;w=w} ->
          match vns with
          | Value_names v ->
             {nmap=nmap;eset=eset;
              symtab=(
                let vv = (List.nth v (curr_level-1)) in
                SM.add vv
                  {val_name=vv;val_ty=5;
                   val_def=aa;def_port=bb+1}
                  sm, pm);typemap=tm;w=w} in
     let in_gr = output_to_boundary
                   ~start_port:(boundary_in_port_count in_gr)
                   [(aa,bb+1,5)] in_gr in
     (aa,bb,cc),in_gr

  | Dot (ie1, ie2) ->
     let _,in_gr =
       do_in_exp in_gr ie1 in
     do_in_exp in_gr ie2

  | Cross (ie1, ie2) ->
     raise (Sem_error "Need to be in a forall context")

and get_lower_lim = function
  | Cross (ie1, ie2) ->
     raise (Sem_error "Cannot be used in a forall context")
  | Dot (ie1, ie2) ->
     get_lower_lim ie1
  | At_exp (ie,_) ->
     raise (Sem_error "Cannot be used in a forall context")
  | In_exp (vn,Exp e) ->
     try
       List.hd e
     with _ ->
       raise (Sem_error "Error while obtaining lower_lim for forall")

and build_alim in_gr =
  (** Helper function to build an ALim node *)
  let in_port_1 =
    let in_array = Array.make 2 "" in
    in_array in
  let out_port_1 =
    let out_array = Array.make 2 "" in
    out_array in
  add_node_2
    (`Simple (
         ALIML, in_port_1, out_port_1,
         [Name "ALimL"])) in_gr

and build_multiarity siz in_gr =
  (** Helper function building a MULTIARITY node *)
  let in_port_1 =
    let in_array = Array.make siz  "" in
    in_array in
  let out_port_1 =
    let out_array = Array.make siz "" in
    out_array in
  add_node_2 (
      `Simple
        (MULTIARITY,in_port_1,out_port_1,
         [Name ("multiARITY_" ^ (string_of_int siz))])) in_gr

and get_ports_unified of_gr basis_gr parent_gr =
  (** Take basis_gr:boundary and add them to of_gr:boundary
        with the same port numbers. Confirm that parent_gr
        contains the symbol, i.e., restrict to outer
        scope variables.*)
  let bin = get_boundary_node basis_gr in
  match bin with
  | (Boundary (in_port_lis,out_port_lis,boundary_p)) ->
     List.fold_right (fun (x,xp,xn) f_gr ->
         if (is_outer_var xn parent_gr) = true
         then
           (let {nmap=nm;eset=es;symtab=(cs,ps);typemap=ttt;w=i} =
              f_gr in
            if (SM.mem xn ps = true) then
              (let {val_ty=t;val_name=_;val_def=_;def_port=_} =
                 SM.find xn ps in
               let f_gr = {nmap=nm;eset=es;symtab=(
                             SM.add xn
                               {val_ty=t;val_name=xn;val_def=0;
                                def_port=xp} cs,ps);
                           typemap=ttt;w=i} in
               add_to_boundary_inputs ~namen:xn 0 xp f_gr)
            else (raise (Sem_error
                           ("Cannot find name in outer scope:"^xn))))
         else f_gr)
       in_port_lis of_gr
  | _ -> of_gr

and tie_outer_scope_to_inner from_gr to_gr to_node =
  (** Tie outer scope variables to forall boundary
      input ports. *)
  let bin = get_boundary_node from_gr in
  match bin with
  | (Boundary (in_port_lis,out_port_lis,boundary_p)) ->
     List.fold_right (fun (yy,yp,xn) o_gr ->
         let (xx,xy,xt),o_gr = get_symbol_id xn o_gr in
         add_edge xx xy to_node yp xt o_gr) in_port_lis to_gr
  | _ -> to_gr

and do_forall inexp bodyexp retexp in_gr =
  (** Use Array input's dimensions to
      set Array output's dimensions*)
  let rec get_cross_exp_lis inexp retl =
    (** Create a list of index expressions.
        Cross would be for nested loops and so would At.*)
    match inexp with
    | Cross (ie1,ie2) ->
       get_cross_exp_lis ie2 ((1,ie1)::retl)
    | At_exp (ie,Value_names vns) ->
       let _,oul =
         List.fold_right
           (fun ae (lev,re) ->
             (lev-1,(lev,inexp)::re)) vns
           (List.length vns,[]) in oul
    | aie ->
       (** single nest case *)
       (1,aie)::retl in

  let generator_array_lowlim
        {nmap=nm;eset=es;symtab=(cs,ps);typemap=ttt;w=i} =
    (** Check if we have an ASCATTER or
        Counted loop in the generator *)
    try
      `ArrLim (
          NM.fold (fun kk vv ooo ->
              match vv with
              | Simple (lab,ASCATTER,_,_,_) ->
                 raise (Val_is_found lab)
              | _ -> ooo) nm 0)
    with Val_is_found xyz -> `AScatt xyz in

  let add_asetl_for_array_res
        outer_gen_gr gen_exp_outer in_gr fx aa tt cc mul_n =
    let aar = generator_array_lowlim outer_gen_gr in
    match aar with
    | `ArrLim xy ->
       print_endline ("ArrLim required for ASETL");
       let ainx = get_lower_lim gen_exp_outer in
       let (ai,ay,at),in_gr = do_simple_exp in_gr ainx in
       let (aa1,bb,ci),in_gr =
         unary_internal 2 fx aa tt in_gr ASETL in
       let in_gr = add_edge ai ay aa1 bb ci in_gr in
       let in_gr =
         if mul_n = 0 then
           (print_endline ("Connect ASETL to boundary:");
            add_to_boundary_outputs aa1 cc tt in_gr)
         else
           (print_endline ("Connect ASETL to MULTIARITY:"
                           ^(string_of_int mul_n));
            add_edge2 aa1 cc mul_n cc tt in_gr) in
       xy,in_gr
    | `AScatt xy ->
       let x,xx,xxx = node_incoming_at_port xy 0 outer_gen_gr in
       let (ix,ij,it),in_gr = build_alim in_gr in
       let in_gr = add_edge x xx ix 0 xxx in_gr in
       let (aa1,bb,ci),in_gr =
         unary_internal 2 fx aa tt in_gr ASETL in
       let in_gr = add_edge ix 0 aa1 1 5 in_gr in
       let in_gr =
         if mul_n = 0 then
            (print_endline ("AScatter ASETL connected to boundary:"^
		 (string_of_int mul_n));
            add_to_boundary_outputs aa1 cc tt in_gr)
         else
            (print_endline ("AScatter ASETL connected to MULTIARITY:"^
		 (string_of_int mul_n));
            add_edge2 aa1 cc mul_n cc tt in_gr) in
       aa1,in_gr in

  let build_gen_graph curr_lev in_gr gen_exp =
    let gen_gr =
      get_ports_unified
        (get_a_new_graph in_gr) in_gr in_gr in
    let xyz,gen_gr =
      do_in_exp ~curr_level:curr_lev gen_gr gen_exp in
    xyz,gen_gr in

  let rec build_forloop inexp bodyexp retexp in_gr =
    match inexp with
    | [] ->
       raise (Sem_error "Internal Compiler Error")
    | (curr_lev,gen_exp_inner)::[] ->
       (** In_Gr Must Be Based On An Outer Gen_Gr. *)
       let _,gen_gr =
         build_gen_graph curr_lev in_gr gen_exp_inner in

       (** Put The Decldefs (Loop Code) In The Body. *)
       let (d,q,t1),body_gr =
         (** Create Body Graph Based On In_Gr. **)
         let body_gr = update_parent_syms gen_gr
                         (get_a_new_graph gen_gr) in

         let body_gr = get_ports_unified
                         body_gr gen_gr gen_gr in

         do_decldef_part body_gr bodyexp in

       (** Insert Expressions Inside Return Clauses To Body Graph. *)
       let body_gr,ret_lis_a,ret_lis_b,ret_lis_c =
         do_returns_clause_list body_gr retexp [] [] [] in

       (** Connect Results To Body's Boundary *)
       let body_gr = output_to_boundary ret_lis_b body_gr in
       (** Connect Results To Body's Boundary *)
       let body_gr = output_to_boundary_with_none ret_lis_c body_gr in

       (** Build Return-Signature To Provide To Outer
           Loop In Order To Build Its Returns Graph. *)
       let ret_lis_a,_,cou =
         List.fold_right
           (fun (y,x,tt) (outL,sm,cou) ->
             if (IntMap.mem x sm = true) then
               (y,tt,(IntMap.find x sm))::outL,sm,cou
             else
               (y,tt,cou)::outL,
               (IntMap.add x cou sm),cou+1) ret_lis_a
           ([],IntMap.empty,1) in

       let ret_lis_c,_,cou =
         List.fold_right
           (fun rrr (outL,sm,cou) ->
             match rrr with
             | Some (x,px,tt) ->
                (if (IntMap.mem x sm = true) then
                   (Some (tt,(IntMap.find x sm)))::outL,sm,cou
                 else
                   (Some (tt,cou))::outL,
                   (IntMap.add x cou sm),cou+1)
             | None -> (None::outL,sm,cou)) ret_lis_c
           ([],IntMap.empty,cou) in

       (** Add gen, body and returns subgraphs
           to the return value, Graph type: "forall_gr". *)
       (** Add Returns Subgraph to Forall Graph. *)
       let (rx,ry,rz), forall_gr, ret_lis_a =
         let forall_gr = get_a_new_graph in_gr in
         add_return_gr forall_gr in_gr ret_lis_a ret_lis_c in

       let (gx,gy,gz), forall_gr =
         add_node_2
           (`Compound(
                gen_gr,INTERNAL,0,
                [Name "GENERATOR"],[])) forall_gr in

       let (bx,by,bz), forall_gr =
         add_node_2
           (`Compound (body_gr,INTERNAL,0,
                       [Name "BODY"],[])) forall_gr in

       let forall_gr =
         get_ports_unified forall_gr body_gr gen_gr in

       (bx,by,bz),ret_lis_a,forall_gr

    | (curr_lev,gen_exp)::gen_exp_tl ->
       let (inner_gen_n,inner_gen_p,inner_gen_ty),
           inner_ret,forall_gr =
         (** Create A Generator For Outer Loop. *)
         let (outer_gen_n,outer_gen_p,outer_gen_ty),gen_gr =
           build_gen_graph curr_lev in_gr gen_exp in

         (** Add outer loop generator to a new forall_gr. *)

         let _,forall_gr =
           let forall_gr = get_ports_unified
                             (get_a_new_graph gen_gr)
                             gen_gr gen_gr in
           add_node_2
             (`Compound(
                  gen_gr,INTERNAL,0,
                  [Name "GENERATOR"],[])) forall_gr in

         let _, inner_ret, body_nest_gr =
         (** As The Body Would Need Outer And Inner Generators,
             Send Gen_Gr To The Recursive Call To Obtain
             The Inner Loop, Which Is Body_Nest_Gr. *)
           build_forloop gen_exp_tl bodyexp retexp
             (get_ports_unified
                (get_a_new_graph gen_gr)
                gen_gr gen_gr) in

         (** Add Returns Graph To Forall_Gr. **)
         let (rx,ay,az), forall_gr, ret_lis_a =
           add_return_gr forall_gr gen_gr inner_ret [] in

         (** Add Body_Nest_Gr In Place Of A "Body" Subgraph. *)
         let (fx,fy,fz), forall_gr =
           add_node_2
             (`Compound (body_nest_gr,INTERNAL,0,
                         [Name "FORALL"],
                         let lis = get_assoc_list body_nest_gr in
                         (List.length lis)::lis)) forall_gr in

         let _, re_ret_lis_a, forall_gr =
           (** Get Generator'S Lower Size Setting
               And Add To Asetl. After That Abstract This
               And Call From Outside As Well. *)
           List.fold_right (
               fun (wh,tt,aa) (cc, outl, in_gr) ->
               match wh with
               | `Array_of ->
                  let ouln,in_gr =
                    add_asetl_for_array_res gen_gr gen_exp
                      in_gr fx aa tt cc 0 in
                  cc+1,(wh,tt,ouln,cc)::outl,in_gr
               | _ ->
                  let in_gr = add_to_boundary_outputs fx cc tt in_gr in
                  cc+1,(wh,tt,fx,cc)::outl,in_gr) ret_lis_a
             (0,[],forall_gr) in

         let forall_gr =
           let forall_gr =
             get_ports_unified
               forall_gr body_nest_gr gen_gr in
           tie_outer_scope_to_inner forall_gr forall_gr fx in

         (fx,fy,fz),ret_lis_a,forall_gr in
       (inner_gen_n,inner_gen_p,inner_gen_ty),inner_ret,forall_gr in

  let acrossl = get_cross_exp_lis inexp [] in
  let xyz,ret_lis_a,forall_gr =
    build_forloop acrossl bodyexp retexp in_gr in
  let forall_gr =
    get_ports_unified forall_gr forall_gr forall_gr in
  let (fx,fy,fz), in_gr =
    add_node_2
      (`Compound (forall_gr,INTERNAL,0,
                  [Name "FORALL"],
                  let lis = get_assoc_list forall_gr in
                  (List.length lis)::lis)) in_gr in

  let (mul_n,mul_p,mul_t),in_gr =
    build_multiarity (List.length ret_lis_a) in_gr in

  let _,re_ret_lis_a,in_gr =
    List.fold_right (
        fun (wh,tt,aa) (cc,outl,iigr) ->
        match wh with
        | `Array_of ->
           print_endline "Adding array_of to FORALL output";
           let ouln,iigr =
             let _,gen_exp =
               try
                 List.hd acrossl
               with _ ->
                 raise (Sem_error ("Error lowering gen_exp")) in
             print_endline ("mul_n:" ^ (string_of_int mul_n));
             add_asetl_for_array_res (get_gen_graph forall_gr)
               gen_exp iigr fx aa tt cc mul_n in
           cc+1,(wh,tt,ouln,cc)::outl,iigr
        | _ ->
           cc+1,(wh,tt,fx,cc)::outl,
           add_edge2 fx aa mul_n cc tt iigr)
      ret_lis_a (0,[],in_gr) in

  let in_gr = tie_outer_scope_to_inner forall_gr in_gr fx in
  Printexc.print_raw_backtrace stdout (Printexc.get_callstack 10);
  print_endline ("Lowered forall to graph:" ^
                 (string_of_triple_int (mul_n,mul_p,mul_t)));
  print_endline (string_of_graph in_gr);
  (mul_n,mul_p,mul_t),ret_lis_a,in_gr

and do_prefix_name in_gr = function
  (** TODO *)
  | Char_prefix -> ((0,0,0), in_gr)
  | Double_prefix -> ((0,0,0), in_gr)
  | Integer_prefix -> ((0,0,0), in_gr)
  | Real_prefix -> ((0,0,0), in_gr)

and do_decldef_part in_gr = function
  | Decldef_part f ->
  (** A list of variable bindings in a LET expression.
      For example,
      LET
      X := 1;
      Y,Z := LET
      X := 2;
      Y := 3 IN
      X + Y,X - Y
      END LET IN
      X * Y + Z
      END LET
      'f' will have an AST looking like:
      f: Ast.decldef list =
      [Decl_def (
           Def (["X"],
           Exp [Constant (Int 1)])
           );
       Decl_def (
           Def (["Y"; "Z"],
           Exp [Let
               (Decldef_part
                  [Decl_def (
                       Def (["X"],
                       Exp [Constant (Int 2)]));
                   Decl_def (
                       Def (["Y"],
                       Exp [Constant (Int 3)]))],
                Exp [Add (Val (Value_name "X"), Val (Value_name "Y"));
                     Subtract (Val (Value_name "X"), Val (Value_name "Y")
      )])]))] *)
     let xyz, in_gr =
       add_each_in_list in_gr f 0 do_decldef
     in xyz,in_gr

and do_def in_gr = function
  | Def (bound_names,y) ->
     (* Things get confusing, no doubt:
     LET
     X := 1;
     Y,Z :=
       LET
         X := 2;
         Y := 3 IN
       X + Y,X - Y
       END LET
     IN
     X * Y + Z
     END LET

     x * y + z for
               (x for x = 1;
               y,z = ( x+y,x-y ) for x = 2, y = 3)
     The exp above without any paren - that is the outer
     one. That use 1 for x, (2+3) for y and (2-3) for z.
     We specify bound values before specifying the
     function's body. Names are shared all over.
     That is all going to add to confusion.
     The numbering technique is not used in this lowering.
     I think it may help.
      *)

     (** WHY ARE MULTIARITY EDGES HERE MISSING TYPES **)
     let named_exp = match y with
       | Exp ee ->
          let (mx,mp,mt),in_gr = do_exp in_gr (Exp ee) in
          print_endline ("EXP EE:\n" ^ (str_exp (Exp ee)));
	  let _ = write_any_dot_file "exp.dot" in_gr in
	  print_endline (string_of_triple_int (mx,mp,mt));
	  print_endline (string_of_node mx in_gr);
          let rec add_multiarity_to_gr (mx,mp,mt) bound_names
     {nmap=nmap;eset=eset;
                     symtab=(umap,vmap);typemap=tm;w=w} =
            match bound_names with
            | [] ->
               (mx,mp,mt),
               {nmap=nmap;eset=eset;
                symtab=(umap,vmap);typemap=tm;w=w}
            | bound_name::tl_names ->
               let in_gr2 = {nmap=nmap;eset=eset;
                     symtab=(umap,vmap);typemap=tm;w=w} in
               let n1,p1,ed_ty =
                 find_incoming_regular_node mx mp mt in_gr2 in
               add_multiarity_to_gr
                 (mx,mp+1,mt) tl_names
                 {nmap=nmap;eset=eset;
                  symtab=(
                    SM.add bound_name
                      {val_name=bound_name;val_ty=ed_ty;
                       val_def=n1;def_port=p1}
                      umap,vmap);typemap=tm;w=w} in
          add_multiarity_to_gr (mx,mp,mt) bound_names in_gr
       | _ ->
          (0,0,0),in_gr in
     named_exp

and get_type_num in_gr = function
  | Ast.Type_name yy ->
     lookup_by_typename in_gr yy
  | Ast.Boolean -> 1
  | Ast.Character -> 2
  | Ast.Real -> 3
  | Ast.Double_real -> 4
  | Ast.Integer -> 5
  | Ast.Null -> 6
  | _ ->
     raise (Node_not_found
              "Unexpected Decl, must never be here")

and do_params_decl po in_gr z =
  match z with
  | Decl(x,y) ->
     let type_num = get_type_num in_gr y in
     match in_gr with
     | {nmap=nmap;eset=eset;symtab=(u,v);typemap=tm; w=w} ->
        let rec add_all_to_sm umap xli p q =
          match xli with
          | hdx::tlx ->
             let sm_v =
               {val_name=hdx;val_ty=type_num;
                val_def=0;def_port=p+po} in
             add_all_to_sm (SM.add hdx sm_v umap) tlx (p+1) (hdx::q)
          | [] -> p,q,umap in
        let p,q,u = add_all_to_sm u x 0 [] in
        ((p+po,q,type_num),
         {nmap=nmap;eset=eset;symtab=(u,v);typemap=tm; w=w})

and do_decl in_gr z =
  print_endline ("Lowering Decl");
  print_endline (str_decl z);
  match z with
  | Decl(x,y) ->
     let type_num = get_type_num in_gr y in
     match in_gr with
     | {nmap=nmap; eset=eset; symtab=(u,v); typemap=tm; w=w} ->
        let rec add_all_to_sm umap xli =
          match xli with
          | hdx::tlx ->
             let sm_v =
               {val_name=hdx;val_ty=type_num;val_def=0;def_port=0} in
             add_all_to_sm (SM.add hdx sm_v umap) tlx
          | [] -> umap in
        let u = add_all_to_sm u x in
        ((0,0,type_num),
         {nmap=nmap; eset=eset; symtab=(u,v); typemap=tm; w=w})

and extract_types_from_decl_list dl =
  List.fold_left (
      fun dlz dlx ->
      dlz @ (match dlx with
               Decl(x,aty) ->
               List.map (fun x -> aty) x)) [] dl

and do_decl_helper in_gr ex1 xl =
  match in_gr with
  | {nmap=nmap;eset=eset;symtab=(umap,v);typemap=tm;w=w} ->
     let umap =
       let existing_rec = SM.find xl umap in
       match existing_rec
       with {val_name=xl;val_ty=aty;val_def=_;def_port=_;} ->
         (SM.add xl
            {val_name=xl;val_ty=aty;val_def=ex1;def_port=0;} umap) in
     umap

and do_decldef in_gr =
  function
  | Decl_def x ->
     print_endline ("Decl_def "^ (str_decldef (Decl_def x)));
     do_def in_gr x
  | Decl_decl x ->
     print_endline ("Decl_decl " ^ (str_decldef (Decl_decl x)));
     do_decl in_gr x
  | Decldef (x,y) ->
     print_endline ("Decldef " ^ (str_decldef (Decldef (x,y))));
     (* this goes inside out *)
     let rec name_list xx =
       match xx with
       | Decl(xxh,xxy)::tlx -> xxh @(name_list tlx)
       | [] -> [] in
     let named_exp =
       match y with
       | Exp ee -> zipem (name_list x) ee
       | _ -> [] in
     let rec add_decl_exp xlis in_gr =
       match xlis with
       | (x,ey)::tl ->
          let (num_node,po,t1), in_gr =
            do_simple_exp in_gr ey in
          (match in_gr with
           | {nmap=nb;eset=eb;symtab=(u,v);typemap=tm;w=w} ->
              add_decl_exp tl
                ({nmap=nb;eset=eb;
                  symtab=(do_decl_helper in_gr num_node x, v);
                  typemap=tm;w=w})
          )
       | [] -> in_gr in
     let (_,_,typenum),in_gr =
       add_each_in_list in_gr x 0 do_decl in
     let ret_val =
       ((0,0,typenum),add_decl_exp named_exp in_gr)
     in ret_val

and do_function_name in_gr = function
  | Function_name f ->
     (** what do we do with the function names **)
     let f = f in
     ((0,0,0), in_gr)

and do_arg in_gr = function
  | Arg e -> do_exp in_gr e

and find_an_union_ty iiee
{nmap=_;eset=_;symtab=_;typemap=(_,tmn,_);w=_} =
  match TM.find iiee tmn with
  | Union (lt,nxt,xx) -> lt
  | _ -> raise (Node_not_found "Union type expected")

and enumerate_union_tags iiee
{nmap=_;eset=_;symtab=_;typemap=(_,tmn,_);w=_} =
  let rec lookup_tags mmm tmn tag_l =
    match TM.find mmm tmn with
    | Union (lt,nxt,xx) ->
       if nxt = 0
       then mmm::tag_l
       else (lookup_tags nxt tmn (mmm::tag_l))
    | _ -> raise (Node_not_found "Union type expected") in
  lookup_tags iiee tmn []

and find_any_ty iii {nmap=_;eset=_;symtab=_;
                     typemap=(_,tmn,_);w=_} =
  TM.find iii tmn

and find_matching_union_str eee tm =
  TM.fold (fun k v z ->
      (match z with
       |  Emp ->
           (match v with
            | Union (lt,nxt,xx) ->
               (match String.equal xx eee with
                | true -> Som k
                | false -> z)
            | _ -> z)
       | _ -> z)) tm Emp

and get_new_tagcase_graph in_gr vntt e =
  let {nmap=nmm;eset=ees;symtab=(cs,ps);
       typemap=tyblob;w=tail} =
    get_a_new_graph in_gr in
  (** We can only add the tagcase Name
      to matched variants. Otherwise
      cannot have access to the union's
      contents at all. So do not add
      the value name to Otherwise. **)
  let in_gr_ =
    match vntt with
    | `AnyTag (vn_n,uniontt,_) ->
       {nmap=nmm;
        eset=ees;
        symtab=
          (SM.add vn_n
             {val_name=vn_n;val_ty=uniontt;
              val_def=0;def_port=0} cs,ps);
        typemap=tyblob;w=tail}
    | `OtherwiseTag ->
       {nmap=nmm;eset=ees;
        symtab=(cs,ps);typemap=tyblob;w=tail} in
  (** There may be an expression list
      returning multiple values in the
      RHS of the variant. Add them the
      way we usually do to the subgraph. **)
  let outs_,in_gr_ = do_exp in_gr_ e in
  let in_gr_ = connect_one_to_one
                 (all_nodes_joining_at
                    outs_ in_gr_)
                 0 in_gr_ in

  (** Add some pragmas -- this may need
      to match what the Sisal developers
      liked to have here -- **)

  let prags_sth = match vntt with
    | `AnyTag (vn_n,_,bii) ->
       [Name
          (List.fold_right
             (fun x y -> cate_nicer x y ",") bii "")]
    | `OtherwiseTag -> [Name "Otherwise"] in
  (** return the output types in jj,
      pragmas and updated graph likewise **)
  outs_,prags_sth,in_gr_

and check_subgr_tys in_gr jj prev =
  Format.printf "FIRST:%s\nNEXT:%s\n"
    (
      IntMap.fold
        (fun ke v z -> (string_of_int ke) ^ ";" ^(string_of_int v) ^ z) jj "")
    (
      IntMap.fold
        (fun ke v z -> (string_of_int ke) ^ ";" ^(string_of_int v) ^ z) prev "");
  let rec do_in_loop curr last jj prev =
    if curr < last then
      if IntMap.mem curr prev = false then
        (raise (Sem_error (
                    Format.printf "PREV does not have %d\n"
                      curr; "")))
      else if IntMap.mem curr jj = false then
        (raise  (Sem_error (
                     Format.printf "JJ does not have %d\n"
                       curr; "")))
      else
        (let fst = IntMap.find curr jj in
         let snd = IntMap.find curr prev in
         if fst != snd then
           raise (Sem_error (
                      Format.printf "%d:%d %d:%d\n"
                        (IntMap.find curr jj)
                        (IntMap.find curr prev);
			"Mismatched types";
			"Loop bug"))
         else
           (Format.printf "Matches: %d:%d %d:%d\n" curr fst curr snd;
            do_in_loop (curr+1) last jj prev))
    else
      () in do_in_loop 0 (IntMap.cardinal jj) jj prev

and boundary_node_lookup {nmap=nm;eset=pe;symtab=(ls,ps);w=pi} =
  let in_lists =
    ES.fold
      (fun ((x,p),(yy,p1),tt) y -> if x = 0 then (x,p)::y else y)
      pe [] in
  let str_names =
    let zzz = AStrSet.empty in
    List.fold_right (
        fun (x,p) z ->
        SM.fold (
            fun
              k {val_ty=_;val_name=str;val_def=jj;def_port=jp} z1 ->
            if (jj = x && jp = p) then
              AStrSet.add str z1
            else z1) ps z) in_lists zzz in
  str_names

and if_type_fail in_gr jj prev =
  raise
    (
      Sem_error
        (
          print_endline (string_of_graph in_gr);
          let k =
            "OUTPUT TYPES OF SELECT DO NOT MATCH: " ^
              " [" ^
                (cate_list
                   (List.map (fun x ->
                        (string_of_int x) ^ ":" ^
                          ( rev_lookup_ty_name x)) prev)
                   ";" ) ^
                  "] [" ^ (cate_list
                             (List.map
                                (fun x ->
                                  (string_of_int x) ^ ":" ^
                                    (rev_lookup_ty_name x))
                                jj) "") ^ "]" in
          print_endline k; k
        )
    )

and new_graph_for_tag_case vn_n t1 in_gr =
  (** Put local symbols of the incoming graph
      into the parent symtab to initialize
      a new graph. **)
  let tagcase_gr_ = unify_syms in_gr in
  let {nmap=nm;eset=ne;symtab=(cs,ps);typemap=tmm;w=tail} =
    tagcase_gr_ in
  let {nmap=nm;eset=ne;symtab=_;typemap=tmn;w=tail}
    = get_a_new_graph tagcase_gr_ in
  let tagcase_gr_ = {nmap=nm;eset=ne;
                     symtab=(SM.empty,ps);typemap=tmm;w=tail} in
  (** add the tagcase's variable name, for example:
      tagcase "P", add P **)
  (** need a new graph here in a compound node **)
  let cs = SM.add vn_n
             {val_name=vn_n;val_ty=t1;val_def=0;def_port=0} cs in
  {nmap=nm;eset=ne;symtab=(cs,ps);typemap=tmm;w=tail}

and lookup_tag_nums tagn tm outs =
  match tagn with
  | [] -> outs
  | hdt::tlt ->
     let looked_up_num hdt tm =
       match (find_matching_union_str hdt tm) with
       | Emp -> raise (Node_not_found
                         "Unknown tag type in an union")
       | Som k -> k in
     lookup_tag_nums tlt tm ((looked_up_num hdt tm)::outs)

and tag_typecheck_fail vn_n in_gr jj prev =
  raise
    (
      Sem_error
        (
          print_endline (string_of_graph in_gr);
          let k =
            "OUTPUT TYPES OF TAGS DO NOT MATCH FOR: " ^
              vn_n ^ " [" ^
                (cate_list
                   (List.map (fun x ->
                        (string_of_int x) ^ ":" ^
                          ( rev_lookup_ty_name x)) prev)
                   ";" ) ^
                  "] [" ^ (cate_list
                             (List.map
                                (fun x ->
                                  (string_of_int x) ^ ":" ^
                                    (rev_lookup_ty_name x))
                                jj) "") ^ "]" in
          print_endline k; k
        )
    )

and check_tag_types vn_n jj prev in_gr =
  if jj = prev then ""
  else raise (Sem_error ("Output types do not match for:"
                         ^ vn_n))

and tag_builder t1 in_gr tagcase_g ex vn_n prev_out_types tag_gr_map =
  (** A recursive visitor that builds subgraphs for each variant
      in the match. **)
  match ex with
  | [] -> prev_out_types,tagcase_g,tag_gr_map
  | hde::tl ->
     let tagcase_gr_ =
       new_graph_for_tag_case vn_n t1 in_gr in
     let jj,prags,tagcase_gr_i,nums =
       match hde with
       | Tag_list (Tagnames tns,e) ->
          let {nmap=_;eset=_;symtab=_;typemap=(_,tm,_);w=_}
            = tagcase_g in
          let nums = lookup_tag_nums tns tm [] in
          (** tag labels that are being matched **)
          let a_tag_ty = find_an_union_ty (
               try List.hd nums with _ ->
                 raise (Sem_error ("error lowering tag_case")))
               tagcase_g in
          (** the output types from each variant is put
              in jj below ---
              all tags need to output the same types--- *)
          let outlis,prags,in_gt_ =
            get_new_tagcase_graph tagcase_gr_
              (`AnyTag (vn_n,a_tag_ty,tns)) e in
          let jj,in_gt_ = extr_types in_gt_ (outlis,IntMap.empty) in
          jj,prags,in_gt_,nums in
     (** There can be a bunch of exps from each tag,
         get the types and compare
         them to make sure that they are the same
         as for each earlier tag-case match *)
     let _ = check_tag_types vn_n jj prev_out_types tagcase_gr_ in
     let (ii,_,_),tagcase_g =
       add_node_2 (`Compound(
                       tagcase_gr_i,INTERNAL,0,prags,[])) tagcase_g in
     let bound_nodes_TC = boundary_node_lookup tagcase_g in
     let tagcase_g = add_edges_to_boundary
                       tagcase_gr_i tagcase_g ii in
     (** map each tagnum to its subgraph,
         this will become the association list **)
     let tag_gr_map = List.fold_right
                        (fun c mm -> IntMap.add c ii mm)
                        nums tag_gr_map in
     tag_builder t1 in_gr tagcase_g tl vn_n jj tag_gr_map

and buildList n =
  let rec get_a_list_of_N acc i =
    if i <= n then
      get_a_list_of_N (i::acc) (i+1)
    else (List.rev acc) in
  get_a_list_of_N [] 0

and add_edges_from_inner_to_outer ty_map outer_gr comp_node namen =
  (** Propagate outputs of inner compound nodes to the
      recursive caller, using MULTIARITY. Make sure that they
      are returned in the expected order.*)
  let in_port_1 =
    let in_array = Array.make (IntMap.cardinal ty_map) "" in
    in_array in
  let out_port_1 =
    let out_array = Array.make (IntMap.cardinal ty_map) "" in
    out_array in
  let (oo,op,ot),outer_gr =
    add_node_2 (
        `Simple
          (MULTIARITY, in_port_1, out_port_1, [Name namen])) outer_gr in
  let outer_gr = IntMap.fold (fun ke ed_ty out_gr ->
                     add_edge comp_node ke oo ke ed_ty out_gr )
                   ty_map outer_gr in
  (oo,op,ot),outer_gr

and add_edges_to_boundary a_gr outer_gr to_node =
  let bound_nodes_a = boundary_node_lookup a_gr in
  let bound_nodes_a_lis =
    AStrSet.fold (fun x y -> x::y) bound_nodes_a [] in
  let sym_ids =
    List.map (fun x ->
        let xx,xxy =
          get_symbol_id x a_gr in xx)
      bound_nodes_a_lis in
  let gr,po =
    List.fold_right (fun (nx,np,nt) (y,i) ->
        ((add_edge nx np to_node i nt y),i+1))
      sym_ids (outer_gr,0) in gr

and get_simple_unary nou in_gr node_tag =
  let in_port_1 =
    let in_array = Array.make 1 "" in
    in_array in
  let out_port_1 =
    let out_array = Array.make nou "" in
    out_array in
  let (z,_,_),in_gr =
    add_node_2 (
        `Simple
          (node_tag,in_port_1,out_port_1,[None])) in_gr in
  ((z,0,0), in_gr)

and unary_internal nou e pi t1 in_gr node_tag =
  let (z,_,_), in_gr = get_simple_unary nou in_gr node_tag in
  let in_gr = add_edge e pi z 0 t1 in_gr in
  ((z,0,t1),in_gr)

and unary_fun nou in_gr e node_tag =
  let (e,pi,t1),in_gr = do_simple_exp in_gr e in
  unary_internal nou e pi t1 in_gr node_tag

and bin_fun a b in_gr node_tag =
  let get_simple_bin in_gr node_tag =
    let in_port_2 =
      let in_array = Array.make 2 "" in
      in_array in
    let out_port_1 =
      let out_array = Array.make 1 "" in
      out_array in
    add_node_2 (
        `Simple
          (node_tag,in_port_2,out_port_1,[None])) in_gr in
  let base_case_bin a b node_tag in_gr =
    let (c,pi1,qq1),i_gr =
      do_simple_exp in_gr a in
    let (d,pi2,qq2),i_gr =
      do_simple_exp i_gr b in
    let (z,_,_), out_gr =
      get_simple_bin i_gr node_tag in
    let c,pi1,qq1 = (match (get_node c i_gr) with
    | Simple (la,MULTIARITY,_,_,_) ->
      first_incoming_triple_to_multiarity c i_gr
    | _ -> c,pi1,qq1) in
    let d,pi2,qq2 = (match (get_node d i_gr) with
    | Simple (la,MULTIARITY,_,_,_) ->
      first_incoming_triple_to_multiarity d i_gr
    | _ -> d,pi2,qq2) in
    (match qq1 = qq2
     with true ->
           (let out_gr =
              add_edge c pi1 z 0 qq1 out_gr in
            let out_gr =
              add_edge d pi2 z 1 qq2 out_gr in
            ((z,0,qq1),out_gr))
        | false ->
           raise (Sem_error (
                      let kkk =
                        cate_list
                          [str_simple_exp ~offset:2 a;
                           " of type:" ^ (string_of_int qq1);
                           str_simple_exp ~offset:2 b;
                           " of type:" ^ (string_of_int qq2)]
                          "\n" in
                      ("Bad type in binary exp:" ^ kkk)))) in
  base_case_bin a b node_tag in_gr

and do_simple_exp in_gr in_sim_ex =
  match in_sim_ex with
  | Constant x -> do_constant in_gr x
  | Not e -> unary_fun 1 in_gr e NOT
  | Negate e -> unary_fun 1 in_gr e NEGATE
  | Pipe (a,b) -> bin_fun a b in_gr ACATENATE
  | And (a,b) ->  bin_fun a b in_gr AND
  | Divide (a,b) -> bin_fun a b in_gr DIVIDE
  | Multiply (a,b) -> bin_fun a b in_gr TIMES
  | Subtract (a,b) -> bin_fun a b in_gr SUBTRACT
  | Add (a,b) -> bin_fun a b in_gr ADD
  | Or (a,b) -> bin_fun a b in_gr OR
  | Not_equal (a,b) -> bin_fun a b in_gr NOT_EQUAL
  | Equal (a,b) -> bin_fun a b in_gr EQUAL
  | Lesser_equal (a,b) -> bin_fun a b in_gr LESSER_EQUAL
  | Lesser (a,b) -> bin_fun a b in_gr LESSER
  | Greater_equal (a,b) -> bin_fun a b in_gr GREATER_EQUAL
  | Greater (a,b) -> bin_fun a b in_gr GREATER
  | Invocation(fn,arg) ->
     (match fn with
      | Function_name f ->
         (match f with
          (*TODO: More libs *)
          | "ARRAY_ADDH" ->
             let in_port_00 = Array.make (1) "" in
             let out_port_00 = Array.make (1) "" in
             let ((n,k,_),in_gr) =
               add_node_2
                 (`Simple (AADDH, in_port_00,
                           out_port_00, [])) in_gr in
             let tt,in_gr =
               match arg with
                | Arg aa ->
                   (match aa with
                    | Exp [fst_exp;last_exp] ->
                       let (l,m,tt),in_gr =
                         do_simple_exp in_gr fst_exp in
                       let (ii,jj,pp),in_gr =
                         do_simple_exp in_gr last_exp in
                       let in_gr = add_edge l m n 0 tt in_gr in
                       let in_gr = add_edge ii jj n 1 pp in_gr in
                       tt,in_gr
                 | _ -> raise (Sem_error
	   	                ("Incorrect usage"^
				 " for array_addh"))) in
             (n,0,tt),in_gr
          | "ARRAY_SIZE" ->
             let in_port_00 = Array.make (1) "" in
             let out_port_00 = Array.make (1) "" in
             let ((n,k,_),in_gr) =
               add_node_2
                 (`Simple (ASIZE, in_port_00,
                           out_port_00, [])) in_gr in
             let _,in_gr =
               match arg with
               | Arg aa ->
                  match aa with
                  | Exp aexps ->
                     List.fold_right(
                         fun x (cou,in_gr) ->
                         let (l,m,tt),in_gr =
                           do_simple_exp in_gr x in
                         cou+1,add_edge l m n cou tt in_gr)
                       aexps (0,in_gr)
                  | _ -> 0,in_gr in
             (n,0,5),in_gr
          | _ ->
         print_endline "INVOCATION:";
         print_endline (str_simple_exp (Invocation(fn,arg)));
         let prags = [Name f] in
         let expl,in_gr =
           (match arg with
            | Arg aa ->
               match aa with
               | Exp aexps ->
                  map_exp in_gr aexps [] do_simple_exp
               | Empty -> ([],in_gr)
           ) in
         let in_port_00 =
           Array.make (List.length expl) "" in
         let ((n,k,_),in_gr) =
           add_node_2
             (`Simple (INVOCATION, in_port_00,
                       out_port_0, prags))
             in_gr in
         let tml = lookup_fn_ty f in_gr in
         let _,mmm = List.fold_right
           (fun ae (lev,re) ->
		(lev-1,(n,lev,ae)::re))
	   (List.rev tml) ((List.length tml)-1,[]) in
         let k123 = List.map (fun x ->
                 print_endline (string_of_triple_int x); x) mmm in
         let _,in_gr = add_edges_in_list expl n 0 in_gr in
         let ((n1,k1,_),in_gr) =
           let in_port_01 =
             Array.make (List.length tml) "" in
           let out_port_01 =
             Array.make (List.length tml) "" in
           add_node_2
             (`Simple (MULTIARITY, in_port_01,
                       out_port_01, prags)) in_gr in
	 let _,in_gr = add_edges_in_list k123 n1 0 in_gr in
	 print_endline "Lowered INVOCATION";
	 print_endline (string_of_graph in_gr);
         (n1,0,0), in_gr))
  | Array_ref (ar_a,ar_b) ->
     let (arr_node,arr_port,att),in_gr = do_simple_exp in_gr ar_a in
     let (res_node,res_port,tt),in_gr_res =
       (match ar_b with
        | Exp ex_lis ->
           let add_basic_arr_elem ((aaa,bbb,att),in_gr) arr_indx =
             let (idxnum,idxport,tt),in_gr =
               do_simple_exp in_gr arr_indx in
             let (arrnum,arrport,_),in_gr =
               add_node_2
                 (`Simple (AELEMENT,
                           Array.make 2 "",
                           Array.make 1 "",
                           []))
                 in_gr in
             let in_gr = add_edge idxnum idxport
                           arrnum 1 tt in_gr in
             let in_gr = add_edge aaa bbb arrnum 0 att in_gr in
             let inner_ty_num =
               match lookup_ty att in_gr with
               | Array_ty ij -> ij
               | _ -> raise (Sem_error (
                                 "Situation:" ^
                                   (string_of_if1_ty
                                      (lookup_ty att in_gr)))) in
             ((arrnum,arrport,inner_ty_num),in_gr) in
           List.fold_left add_basic_arr_elem
             ((arr_node,arr_port,att),in_gr) ex_lis
        | _ -> ((arr_node,arr_port,att),in_gr)) in
     ((res_node,res_port,tt),in_gr_res)

  | Let (dp,e) ->
     let {nmap=nm;eset=pe;symtab=sm;typemap=tm;w=pi} = in_gr in
     let x,in_gr = do_decldef_part in_gr dp in
     let (xx,xy,xz),in_gr = do_exp in_gr e in
     let {nmap=nm;eset=pe;symtab=_;typemap=tm;w=pi} = in_gr in
     let in_gr = {nmap=nm;eset=pe;symtab=sm;typemap=tm;w=pi} in
     (xx,xy,xz),in_gr

  | Old (Value_name v) ->
     do_val_internal in_gr (`OldMob v)

  | Val v ->
     do_val in_gr v
  | Paren e ->
     do_exp in_gr e

  | Array_generator_named tn ->
     let (bb,pp,_),in_gr =
       add_node_2
         (`Simple(ABUILD,
                  (Array.make 1 ""),
                  Array.make 1 "",[])) in_gr in
     let tt = lookup_by_typename in_gr tn in
     print_endline ("Array_gen:" ^
   	            (str_simple_exp (Array_generator_named tn)));
     print_endline ("Type:"^ (string_of_int tt));
     (bb,pp,tt),in_gr

  | Array_generator_named_addr (tn,ep) ->
     print_endline ("Array_generator_named_addr:" ^
   	            (str_simple_exp (
                       Array_generator_named_addr(tn,ep))));
     let tn = tn in
     array_builder_exp ~inc_typ:(lookup_by_typename in_gr tn ) in_gr ep

  | Array_generator_unnamed ep ->
     print_endline ("Array_generator_unnamed:" ^
   	            (str_simple_exp (
                       Array_generator_unnamed ep)));
     array_builder_exp in_gr ep

  | Array_replace (p,epl) ->
     let (sn,sp,t1),in_gr = do_simple_exp in_gr p in
     let rec do_array_replace ((sn,sp,t1),in_gr) =
       function
       | SExpr_pair (idx,values)::tl ->
          let (al,ap,t1),in_gr =
            (match values with
             | Empty ->
                raise (Node_not_found
                         "badly formed array replace")
             | Exp aexp ->
                let bbu,in_gr =
                  map_exp in_gr aexp [] do_simple_exp in
                let (idxnum,idxport,t1),in_gr =
                  do_simple_exp in_gr idx in
                let (bb,pp,_),in_gr =
                  add_node_2
                    (`Simple(
                         AREPLACE,
                         (Array.make ((List.length aexp)+2) ""),
                         Array.make 1 "",[]))
                    in_gr in
                let in_gr =
                  add_edge idxnum idxport bb 1 0
                    (add_edge sn sp bb 0 0 in_gr) in
                add_edges_in_list bbu bb 2 in_gr) in
          let (tan,tap,t1),in_gr =
            do_array_replace ((al,ap,0),in_gr) tl
          in (tan,tap,0),in_gr
       | [] -> (sn,sp,0),in_gr in
     do_array_replace ((sn,sp,0),in_gr) epl

  | Record_ref (e,fn) ->
     let fn = match fn with
       | Field_name fn -> fn in
     let (ain,apo,tt1),in_gr = do_simple_exp in_gr e in
     let _,tt2 = get_record_field in_gr tt1 fn in
     let (bb,pp,tti),in_gr =
       let in_porst = Array.make 2 "" in
       in_porst.(0) <- fn;
       add_node_2 (`Simple(
                       RELEMENTS,in_porst,
                       Array.make 1 "",[None])) in_gr in
     (bb,pp,tt2),(add_edge ain apo bb 1 tt1 in_gr)

  | Record_generator_primary (e,fdle) ->
     let (e,p,tt),in_gr = do_simple_exp in_gr e in
     let rec do_each_field ((a,b,tt),in_gr) = function
       | Field_exp (Field fi,se)::tl ->
          let (aseb,asep,finaltt),in_gr = do_simple_exp in_gr se in
          let rec do_field_chain ((fe,ff,tt),in_gr) = function
            | (Field_name fna)::tll ->
               let (bb,bp,_),in_gr =
                 let in_porst = Array.make 3 "" in
                 in_porst.(1) <- fna;
                 let (bb,bp,_),in_gr =
                   add_node_2 (
                       `Simple (
                           RREPLACE,in_porst,
                           Array.make 1 "",[None])) in_gr in
                 (bb,bp,tt),add_edge fe ff bb 0 tt in_gr in
               let t1,t2 = get_record_field in_gr tt fna in
               (** Below tt must be field name's id **)
               do_field_chain ((bb,bp,t1),in_gr) tll
            | [] -> (fe,ff,finaltt),
                    add_edge aseb asep fe 2 finaltt in_gr in
          do_each_field (do_field_chain ((a,b,tt),in_gr) fi) tl
       | [] -> (a,b,tt),in_gr in
     do_each_field ((e,p,tt),in_gr) fdle

  | Record_generator_unnamed (fdl) ->
     record_builder in_gr fdl Emp

  | Record_generator_named (tn,fdl) ->
     (** We can look up tn against known types.
         Following that we may have to thread in
         the record type to the builder to check that the
         return types are correct. **)
     let xx = lookup_by_typename in_gr tn in
     record_builder in_gr fdl (Som xx)

  | Stream_generator tn ->
     let tn = tn in
     add_node_2 (
         `Simple (SBUILD,Array.make 1 "",
                  Array.make 1 "",[None])) in_gr

  | Stream_generator_exp (tn,aexp) ->
     let tn = tn in
     let myll,in_gr = match aexp with
       | Exp axep -> map_exp in_gr axep [] do_simple_exp
       | _ -> [],in_gr in
     do_each_exp_in_strm in_gr myll

  | Stream_generator_unknown_exp aexp ->
     let myll,in_gr = match aexp with
       | Exp axep -> map_exp in_gr axep [] do_simple_exp
       | _ -> [],in_gr in
     do_each_exp_in_strm in_gr myll

  | Union_generator (tn,te) ->
     (** Parameter port assignments are missing.
         Union's tag is missing in RBUILD
         Are we supposed to use RBUILD? **)
     let xx = lookup_by_typename in_gr tn in
     union_builder in_gr te (Som xx)

  | Tagcase (ae,tc,o) ->
     (** Each tag is a graph, tagcase is a
      compound graph with one "input",
      which is the union. So while creating
      a graph for a tag, we have to provide
      the tag's type as the incoming type in its
      boundary--- will need to get a symbol name from
      tagcase_exp and an union type from the RHS
      add the vn_n as a symtab entry of type tyy
      will need to add the above symbol name to the
      boundaries of a new graph and set the type from the
      tag name. **)
     let (a,ap,aunion_type),in_gr,vn_n =
       match ae with
       | Assign(vn,e) ->
          let vn_n = match vn with Value_name vnn -> vnn in
          let (an,po,tyy),in_gr = do_simple_exp in_gr e in
          (an,po,tyy),in_gr,vn_n
       | Tagcase_exp (exp) ->
          raise (Node_not_found "what do we do here") in
     (** Walk over typemap lists and collect
         the union's tag#s **)
     let tag_nums = enumerate_union_tags aunion_type in_gr in
     (** The tags follow the union type in
         the above list, but
         the list needs reversing first. **)
     let tag_nums = List.tl (List.rev tag_nums) in
     (** get one subgraph for each tag in the variant
         cases, except for otherwise, which follows
         down below. The function that generates the
         subgraphs is tag_builder. It adds the subgraphs
         to the newly setup graph: tagcase_gr_.**)
     let output_type_list,tagcase_gr_,tag_map =
       let tagcase_gr_ =
         new_graph_for_tag_case vn_n aunion_type in_gr in
       tag_builder aunion_type in_gr tagcase_gr_
         tc vn_n IntMap.empty
         IntMap.empty in
     (match o with
      | Otherwise e ->
         let (outlis,ii,gr_o) =
           get_new_tagcase_graph
             tagcase_gr_
             (`OtherwiseTag) e in
         let jj,gr_o = extr_types gr_o (outlis,IntMap.empty) in
         let _ = check_tag_types vn_n jj output_type_list in
         let (aa,bb,cc),tagcase_gr =
           add_node_2
             (`Compound(
                  gr_o,INTERNAL,0,
                  [Name "OTHERWISE"],[])) tagcase_gr_ in
         (** Build assoc_list: tag_builder would have
             a key-value for the listed variants
             and remaining would be
             using the Otherwise subgraph.**)
         let assoc_lis =
           List.fold_right
             (fun x outl ->
               match IntMap.mem x tag_map with
               | true ->
                  (IntMap.find x tag_map)::outl
               | false ->
                  aa::outl)
             tag_nums [] in
         let (fin_node,fin_por,fin_tyy),out_gr =
           add_node_2 (`Compound
                         (tagcase_gr,TAGCASE,0,
                          [Name "TAGCASE"],assoc_lis)) in_gr in
         let bound_nodes_TC = boundary_node_lookup tagcase_gr in

         let tagcase_g = add_edges_to_boundary
                           tagcase_gr out_gr fin_node in
         (fin_node,fin_por,fin_tyy),tagcase_g)

  | Is (tn,e) ->
     let tn = tn in
     do_exp in_gr e

  | Prefix_operation (pn,e) ->
     let (n,p,_),in_gr = do_prefix_name in_gr pn in
     do_exp in_gr e

  | Is_error e ->
     do_exp in_gr e

  | If (cl, Else el) ->
     (** Work an example with [1,2]
         and [1,2,3] and [1,2,3,4] **)
     (** How are outputs tied to the
         compound node's outputs?
         Same with inputs **)
     print_endline ("Lowering If-else\n" ^
                      (str_if cl) ^
                        (str_else (Else el)));
     let rec if_builder cl xyz in_gr_if els curr_num
               ty_lis_ret =
       (match cl with
        | (Cond (predicate,body))::tl ->
           print_endline ("Lower predicated body\n" ^
                            (str_if cl));
           (** Provide a new graph to add tl to it **)
           let ty_lis_ret,else_outs,else_gr =
             let grr_th = get_a_new_graph in_gr_if in
             if_builder tl xyz grr_th els
               (curr_num+1) ty_lis_ret in
           let bound_nodes_else = boundary_node_lookup
                                    else_gr in
           let point_edges_to_boundary frm elp elt in_gr =
             match get_node frm in_gr with
             | Simple (_,MULTIARITY,_,_,_) ->
                (*In case frm is a MULTIARITY, redirect
                  incoming edges to the boundary node.*)
                let  {nmap=nm;eset=pe;symtab=sm;typemap=tm;w=pi}
                  = in_gr in
                let unwanted_edges
                  = (all_edges_ending_at frm in_gr) in
                let in_str = ES.fold
                               (fun hde res ->
                                 let (x,xp),(y,yp),yt = hde in
                                 ("(" ^ (string_of_int x) ^ "," ^
                                    (string_of_int xp) ^
                                      ") -> (" ^
                                        (string_of_int y) ^
                                          "," ^
                                            (string_of_int yp) ^
                                          ") of type: " ^
                                            (string_of_int yt)
                                            ^ "\n") ^ res)
                               unwanted_edges "" in
                print_endline ("Incoming edges to boundary:"
                               ^ in_str);
                (*let nes = ES.diff pe unwanted_edges in*)
                let nes = pe in
                let red_nes,_ = redirect_edges 0
                                  unwanted_edges in
                let nes = ES.union nes red_nes in
                {nmap=nm;eset=nes;
                 symtab=sm;typemap=tm;w=pi}
             | _ -> add_edge frm elp 0 0 elt in_gr in

           let els,elp,elt = else_outs in
           let _,else_p,else_t
             = find_incoming_regular_node
                 els elp elt else_gr in
           let ty_lis_else,else_gr =
             extr_types else_gr
               (else_outs,IntMap.empty) in
           let else_gr = point_edges_to_boundary
                           els elp elt else_gr in

           let (else_n,_,_),in_gr_if =
             add_node_2
               (`Compound(
                    else_gr,
                    INTERNAL,0,
                    [Name ("ELSE"^
                             (string_of_int curr_num))],[]))
               in_gr_if in

           (* TODO:What is the context for this *)
          let in_gr_if
             = add_edges_to_boundary
                 else_gr in_gr_if else_n in
           let in_outs,then_gr
             = do_exp
                 (get_a_new_graph in_gr_if)
                 body in
           let ty_lis_then,then_gr
             = extr_types then_gr
                 (in_outs,IntMap.empty) in

           let then_s,then_p,then_t = in_outs in
           let then_s,then_p,then_t =
             find_incoming_regular_node then_s then_p then_t
               then_gr in
           let then_gr = point_edges_to_boundary
                           then_s then_p then_t then_gr in

           let (then_n,_,_),in_gr_if =
             add_node_2
               (`Compound(
                    then_gr,
                    INTERNAL,0,
                    [Name ("BODY"^
                             (string_of_int curr_num))],[]))
               in_gr_if in

           let in_gr_if = add_edges_to_boundary
                            then_gr in_gr_if then_n in
           let _ = check_subgr_tys in_gr_if
                     ty_lis_then ty_lis_else in

           let pred_out,predicate_gr =
             do_exp (get_a_new_graph in_gr_if) predicate in

           let ty_lis,predicate_gr =
             extr_types predicate_gr (pred_out,IntMap.empty) in

           let pred_s,pred_p,pred_t = pred_out in
           let _,pp,pt =
             find_incoming_regular_node
                 pred_s pred_p pred_t predicate_gr in
           let predicate_gr =
             point_edges_to_boundary
               pred_s pred_p pred_t predicate_gr in
           let (pn,_,_),in_gr_if =
             add_node_2
               (`Compound(
                    predicate_gr,
                    INTERNAL,0,
                    [Name ("PREDICATE" ^ (string_of_int
                                            curr_num))],[]))
               in_gr_if in
           let in_gr_if = add_edges_to_boundary
                            predicate_gr in_gr_if pn in
           (*write_any_dot_file "if.dot" in_gr_if;
             write_any_dot_file "then.dot" then_gr;
             write_any_dot_file "else.dot" else_gr;*)
           print_endline "Lowered If-else\n";
           let in_gr_if = output_to_boundary
                            [(pn,pp,pt);
                             (else_n,else_p,else_t);
                             (then_n,then_p,then_t)]
                            in_gr_if in

           ty_lis_then,in_outs, in_gr_if
        | [] ->
           print_endline "Lowering else first";
           print_endline "else";
           print_endline (str_exp els);
           let xyz,i_gr =
             do_exp in_gr_if els in
           let ty_lis,i_gr = extr_types i_gr (xyz,IntMap.empty) in
           ty_lis,xyz,i_gr
       ) in
     let sai,gai =
       let ty_lis,xzy,regar =
         let regar = get_a_new_graph in_gr in
         if_builder cl (0,0,0) regar el 0 [] in
       let boundary_ooo =
         (match regar with
            {nmap=nm;eset=pe;symtab=sm;typemap=tm;w=pi} ->
            (match NM.find 0 nm with
             | Boundary (_,[(pn,pp);(else_n,else_p);
                            (then_n,then_p)],_) ->
                [3;pn;else_n;then_n]
             | _ -> [])) in
       let (sn,sp,st),in_gr =
         add_node_2 (
             `Compound (regar,
                        INTERNAL,0,
                        [Name "SELECT"],boundary_ooo)) in_gr in
       add_edges_from_inner_to_outer ty_lis in_gr sn "SELECT" in
     sai,gai

  | For_all (i,d,r) ->
     (** First we build a hierarchy based on in-exps,
         then we add the body/returns in it. Perhaps
         we could do this easily... i am not sure yet **)
     print_endline "Lowering forall:";
     print_endline (str_simple_exp (For_all(i,d,r)));
     let (fx,fy,fz),ret_lis,in_gr =
       do_forall i d r in_gr in
     (* TODO: Need To Check Vs If1, Add Assoc List *)
     (** How Do We Tie Up Results To Calling Function
         Or To A Let Var *)
     write_any_dot_file "snd.dot" in_gr;
     print_endline "Lowered forall:";
     print_endline (str_simple_exp (For_all(i,d,r)));
     print_endline (string_of_graph in_gr);
     print_endline ("Triple:" ^ (string_of_triple_int (fx,fy,fz)));
     (fx,fy,fz),in_gr

  | For_initial (d,i,r) ->
     let add_decls in_gr dp =
       let build_init_graph in_gr =
         let init_gr =
           get_ports_unified
             (get_a_new_graph in_gr) in_gr in_gr in
         init_gr in
       let xyz,out_gr =
         do_decldef_part (build_init_graph in_gr) dp in
       let _,out_gr =
         let {nmap=_;eset=_;symtab=(cs,ps);typemap=_;w=_} =
           out_gr in
         SM.fold (fun k {val_name=vn_n;
                         val_ty=t1;
                         val_def=dd;
                         def_port=dp}
                      (op,out_gr) ->
             if dd != 0 then
               (op+1,add_edge dd dp 0 op t1 out_gr)
             else (op,out_gr))
           cs (boundary_in_port_count out_gr,out_gr) in
       xyz,out_gr in

     let add_terminator init_gr t =
       let build_term_graph init_gr =
         let term_gr =
           get_ports_unified
             (get_a_new_graph init_gr) init_gr init_gr in
         update_parent_syms init_gr term_gr in
       let (tn,tp,tt),init_gr =
         do_termination (build_term_graph init_gr) t in
       (tn,tp,tt),output_to_boundary [(tn,tp,tt)] init_gr in

     let add_body init_gr bi rclau =
       let build_body_graph init_gr =
         let body_gr =
           get_ports_unified
             (get_a_new_graph init_gr) init_gr init_gr in
         update_parent_syms init_gr body_gr in
       let (bn,bp,bt),body_gr =
         do_iterator (build_body_graph init_gr) bi in

       let body_gr,ret_lis_a,ret_lis_b,ret_lis_c =
         do_returns_clause_list body_gr rclau [] [] [] in
       (* TODO: ret_lis_c *)
       let body_gr = output_bound_names_for_subgraphs ret_lis_b body_gr in
       (** Build Return-Signature To Provide To Outer
           Loop In Order To Build Its Returns Graph. *)
       let ret_lis_a,_,_ =
         List.fold_right
           (fun (y,x,tt) (outL,sm,cou) ->
             if (IntMap.mem x sm = true) then
               (y,tt,(IntMap.find x sm))::outL,sm,cou
             else
               (y,tt,cou)::outL,
               (IntMap.add x cou sm),cou+1) ret_lis_a
           ([],IntMap.empty,1) in
       body_gr,ret_lis_a,ret_lis_b,ret_lis_c in

     let add_ret in_gr ret_lis_a ret_lis_c =
       let for_gr = get_a_new_graph in_gr in
       add_return_gr for_gr in_gr ret_lis_a ret_lis_c in

     let add_comp_node to_gr in_gr namen =
       add_node_2
         (`Compound (in_gr, INTERNAL,0,
                     [Name namen],[])) to_gr in

     let loopAOrB i in_gr = match i with
       | Iterator_termination (ii,t) ->
          let (dn,dp,dt),decl_gr = add_decls in_gr d in
          let (tn,tp,tt),test_gr = add_terminator decl_gr t in
          let body_gr,ret_lis_a,ret_lis_b,ret_lis_c = add_body test_gr ii r in
          let (rx,ry,rt),for_gr,ret_lis_a = add_ret body_gr ret_lis_a [] in
          let (bx,by,bz),for_gr =
            add_comp_node for_gr body_gr "BODY" in
          let (tx,ty,tz),for_gr =
            add_comp_node for_gr test_gr "TEST" in
          let (ix,iy,iz),for_gr = add_comp_node for_gr decl_gr "INIT" in
          let for_gr =
              get_ports_unified for_gr body_gr decl_gr in

          let (fx,fy,fz),in_gr =
            add_node_2
              (`Compound (for_gr, INTERNAL,0,
                          [Name "LoopA"],
                          let lis = get_assoc_list_loopAOrB for_gr in
                          (List.length lis)::lis)) in_gr in
          let (mul_n,mul_p,mul_t),in_gr =
            build_multiarity (List.length ret_lis_a) in_gr in

          let _,re_ret_lis_a,in_gr =
            List.fold_right (
                fun (wh,tt,aa) (cc,outl,iigr) ->
                cc+1,(wh,tt,fx,cc)::outl,
                add_edge2 fx aa mul_n cc tt iigr)
              ret_lis_a (0,[],in_gr) in
          let in_gr = tie_outer_scope_to_inner for_gr in_gr fx in
          (mul_n,mul_p,mul_t),in_gr
       | Termination_iterator (t,ii) ->
          let (dn,dp,dt),decl_gr = add_decls in_gr d in
          let (tn,tp,tt),test_gr = add_terminator decl_gr t in
          let body_gr,ret_lis_a,ret_lis_b,ret_lis_c = add_body test_gr ii r in
          let (rx,ry,rt),for_gr,ret_lis_a = add_ret body_gr ret_lis_a [] in
          let (bx,by,bz),for_gr =
            add_comp_node for_gr body_gr "BODY" in
          let (tx,ty,tz),for_gr =
            add_comp_node for_gr test_gr "TEST" in
          let (ix,iy,iz),for_gr =
            add_comp_node for_gr decl_gr "INIT" in
          let for_gr =
              get_ports_unified for_gr body_gr in_gr in

          let (fx,fy,fz),in_gr =
            add_node_2
              (`Compound (for_gr, INTERNAL,0,
                          [Name "LoopB"],
                          let lis = get_assoc_list_loopAOrB for_gr in
                          (List.length lis)::lis)) in_gr in

          let (mul_n,mul_p,mul_t),in_gr =
            build_multiarity (List.length ret_lis_a) in_gr in

          let _,re_ret_lis_a,in_gr =
            List.fold_right (
                fun (wh,tt,aa) (cc,outl,iigr) ->
                cc+1,(wh,tt,fx,cc)::outl,
                add_edge2 fx aa mul_n cc tt iigr)
              ret_lis_a (0,[],in_gr) in

          let in_gr = tie_outer_scope_to_inner for_gr in_gr fx in
          (mul_n,mul_p,mul_t),in_gr in
     loopAOrB i in_gr

and find_in_graph_from_pragma in_gr namen =
  match in_gr with
    {nmap=nm;eset=ne;symtab=sm;typemap=(t,tm,tmn);w=tail} ->
    let rec gen_gr tl =
      if tl = tail then `Nth
      else
        (let agr = NM.find tl nm in
         match agr with
         | Compound (lab,sy,ty,pl,g,assoc) ->
            if (try List.hd pl with _ ->
               raise (Sem_error ("Error lowering for pragma"))) =
              Name namen then
              `Found_one (lab,sy,pl,g,assoc)
            else gen_gr (tl+1)
         | _ -> gen_gr (tl+1)) in
    gen_gr 0

and do_return_exp in_gr = function
  | Value_of (d,r,e) ->
     let d =
       (match d with
        | No_dir -> `JustReduce
        | Left -> `RedLeft
        | Right -> `RedRight
        | Tree -> `RedTree) in
     let reduc_n =
       (match r with
        | Sum -> "sum"
        | Product -> "product"
        | Least -> "least"
        | Greatest -> "greatest"
        | Catenate -> "catenate"
        | No_red -> "NoRed") in
     let (val_of,val_po,val_ty), in_gr =
       do_simple_exp in_gr e in
     (if String.equal reduc_n "NoRed"
      then
        `FinalVal, (val_of,val_po,val_ty), in_gr
      else
        `Reduce (d,reduc_n), (val_of,val_po,val_ty), in_gr)
  | Array_of e ->
     (** AGATHER GETS HERE **)
     (** TODO HERE I NEED TO BUILD A ARRAY TYPE **)
     let (an,ap,at),in_gr = do_simple_exp in_gr e in
     `Array_of, (an,ap,at), in_gr
  | Stream_of e ->
     (** STREAM GETS HERE **)
     let (sn,sp,st),in_gr = do_simple_exp in_gr e in
     `Stream_of, (sn,sp,st), in_gr

and add_return_gr in_gr body_gr ret_lis_a ret_lis_c =
  let ret_gr = copy_cs_syms_to_cs in_gr
                 (get_a_new_graph body_gr) in
  (* NEED TO ADD STREAM RETURN *)
  let do_reduc ((rdx,red_fn),tt,aa) msk_input in_gr =
    let out_port_1 =
      let out_array = Array.make 1 "" in
      out_array in
    let which_ins = match rdx with
      | `JustReduce -> REDUCE
      | `RedLeft -> REDUCELEFT
      | `RedRight -> REDUCERIGHT
      | `RedTree  -> REDUCETREE in
    let (dd,ee,ff),in_gr =
      add_node_2 (
          `Simple (
              which_ins,
              Array.make(2) "",
              Array.make(1) "",[None])) in_gr in
    let (lx,ly,lz),in_gr =
      add_node_2 (
          `Literal
            (CHARACTER,red_fn,out_port_1)) in_gr in
    let in_gr = add_edge lx ly dd 0 (lookup_tyid CHARACTER) in_gr in
    let in_gr = add_edge 0 aa dd 1 tt in_gr in
    add_to_boundary_outputs dd ee tt in_gr in
  let ret_gr,in_count,out_count,out_lis =
    let rec create_return_nodes
              out_gr in_count out_count
              out_lis ret_lis_a ret_lis_c =
      match ret_lis_a,ret_lis_c with
      | [],[] ->
         out_gr,in_count,out_count,out_lis
      | hd_a::tl_ret_lis_a, hd_c::tl_ret_lis_c ->
         (match hd_a with
          | `Array_of, tt, aa ->
             let (dd,ee,ff),out_gr =
               add_node_2 (
                   `Simple (
                       AGATHER,
                       Array.make(2) "",
                       Array.make(1) "",[None])) out_gr in
             (** Create a type for AGATHER HERE AND ADD ITS TYPE TO
                output ret_lis_a **)
             let what_ty = find_ty in_gr (Array_ty tt) in
             let out_gr = add_edge 0 0 dd 0 5
                            (*integer type for indx*) out_gr in
             let out_gr = add_edge 0 aa dd 1 tt out_gr in
             let out_gr = add_to_boundary_outputs dd ee what_ty out_gr in
             let out_gr =
               (match hd_c with
                | Some (aty,pnum) -> add_edge 0 pnum dd 2 aty out_gr
                | None -> out_gr) in
             create_return_nodes out_gr (in_count+2) (out_count+1)
            (out_lis@[`Array_of, what_ty, aa]) tl_ret_lis_a tl_ret_lis_c
          | `FinalVal, tt, aa ->
             let out_gr =
               (let (dd,ee,ff),out_gr =
                  add_node_2 (
                      `Simple (
                          FINALVALUE,
                          Array.make(2) "",
                          Array.make(1) "",[None])) out_gr in
                let out_gr = add_edge 0 aa dd 0 tt out_gr in
                add_to_boundary_outputs dd ee tt out_gr) in
             create_return_nodes out_gr (in_count+1) (out_count+1)
               (out_lis@[`FinalVal, tt, aa])
               tl_ret_lis_a tl_ret_lis_c
          | `Reduce (`JustReduce, red_fn), tt, aa ->
             let out_gr = do_reduc ((`JustReduce,red_fn),tt,aa) hd_c in_gr in
             create_return_nodes out_gr (in_count+1) (out_count+1)
               (out_lis@[`Reduce (`JustReduce, red_fn),tt,aa])
               tl_ret_lis_a tl_ret_lis_c
          | `Reduce (`RedLeft, red_fn), tt, aa ->
             let out_gr = do_reduc ((`RedLeft,red_fn),tt,aa) hd_c in_gr in
             create_return_nodes out_gr (in_count+1) (out_count+1)
               (out_lis@[`Reduce (`RedLeft, red_fn),tt,aa])
               tl_ret_lis_a tl_ret_lis_c
          | `Reduce (`RedRight, red_fn), tt, aa ->
             let out_gr = do_reduc ((`RedRight,red_fn),tt,aa) hd_c in_gr in
             create_return_nodes out_gr (in_count+1) (out_count+1)
               (out_lis@[`Reduce (`RedRight, red_fn),tt,aa])
               tl_ret_lis_a tl_ret_lis_c
          | `Reduce (`RedTree, red_fn), tt, aa ->
             let out_gr = do_reduc ((`RedTree,red_fn),tt,aa) hd_c in_gr in
             create_return_nodes out_gr (in_count+1) (out_count+1)
               (out_lis@[`Reduce (`RedTree, red_fn),tt,aa])
               tl_ret_lis_a tl_ret_lis_c
          | `Stream_of, tt, aa ->
             create_return_nodes out_gr (in_count+1) (out_count+1)
               (out_lis@[`Stream_of, tt, aa])
               tl_ret_lis_a tl_ret_lis_c)
         | _,_ ->
            raise (Sem_error "Invalid combination for return graph") in
    create_return_nodes ret_gr 0 0 [] ret_lis_a ret_lis_c in

  let xyz, in_gr =
    add_node_2
      (`Compound(ret_gr,INTERNAL,0,
                 [Name "RETURN"],[])) in_gr in
  xyz,in_gr,out_lis

and get_gen_graph in_gr =
  let xyz =
    find_in_graph_from_pragma in_gr "GENERATOR" in
  match xyz with
    `Found_one (lab,sy,pl,g,assoc) -> g
  | `Nth -> raise (
                Sem_error
                  ("Didnt find Generator in In loop"))

and get_assoc_list_loopAOrB inner_gr =
  let body_lab =
    let xyz =
      find_in_graph_from_pragma inner_gr "BODY" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) -> lab
    | `Nth ->
       raise (Sem_error ("Didnt find Body in for loop")) in
  let test_lab =
    let xyz =
      find_in_graph_from_pragma inner_gr "TEST" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) -> lab
    | `Nth ->
       raise (Sem_error ("Didnt find Test in for loop")) in
  let init_lab =
    let xyz =
      find_in_graph_from_pragma inner_gr "INIT" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) -> lab
    | `Nth ->
       raise (Sem_error ("Didnt find Init in for loop")) in
  let ret_lab =
    let xyz =
      find_in_graph_from_pragma inner_gr "RETURN" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) -> lab
    | `Nth ->
       raise (Sem_error ("Didnt find RETURN in for loop")) in
  [init_lab;test_lab;body_lab;ret_lab]

and get_assoc_list inner_gr =
  let gen_lab =
    let xyz =
      find_in_graph_from_pragma inner_gr "GENERATOR" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) ->
       lab
    | `Nth ->
       raise (Sem_error ("Didnt find Generator in Inner loop")) in

  let for_lab =
    let xyz =
      find_in_graph_from_pragma inner_gr "FORALL" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) ->
       lab
    | `Nth ->
       let xyz =
         find_in_graph_from_pragma inner_gr "BODY" in
       match xyz with
       | `Nth ->
          raise (Sem_error ("Didnt find Body in Inner loop"))
       | `Found_one (lab,sy,pl,g,assoc) ->
          lab in

  let for_returns =
    let xyz =
      find_in_graph_from_pragma inner_gr "RETURN" in
    match xyz with
      `Found_one (lab,sy,pl,g,assoc) ->
       lab
    | `Nth ->
       raise (Sem_error ("Didnt find Returns in Inner loop")) in
  [gen_lab;for_lab;for_returns]

and do_returns_clause in_gr ret_clause =
  match ret_clause with
  | Old_ret (re,mc) ->
     raise (Node_not_found "Dont know how to handle this one");
  | Return_exp (re,mc) ->
     let msk,in_gr =
       match mc with
       | Unless an_exp ->
          let in_port_00 = Array.make (1) "" in
          let out_port_00 = Array.make (1) "" in
          let (un,up,uty),in_gr = do_simple_exp in_gr an_exp in
          let (un_,_,_),in_gr =
            add_node_2
              (`Simple
                 (NOT,
                  in_port_00,out_port_00,[]))
              in_gr in
          let in_gr = add_edge un up un_ 0 uty in_gr in
          (Some (un_,0,lookup_tyid BOOLEAN)),in_gr
       | When an_exp ->
          let when_tup,in_gr = do_simple_exp in_gr an_exp in
          (Some when_tup),in_gr
       | No_mask ->
          None, in_gr in
     let aa,bb,in_gr = do_return_exp in_gr re in
     aa,bb,msk,in_gr

and do_returns_clause_list in_gr ret_clause_list ret_lis_a ret_lis_b ret_lis_c =
  (** ret_lis_a, ret_lis_b, ret_lis_c *)
  match ret_clause_list with
  | hd::tl ->
     let xx,(yy,yp,yt),ss,in_gr = (do_returns_clause in_gr hd) in
     do_returns_clause_list in_gr tl
       ((xx,yy,yt)::ret_lis_a) ((yy,yp,yt)::ret_lis_b) (ss::ret_lis_c)
  | [] -> in_gr, ret_lis_a, ret_lis_b, ret_lis_c

and do_defines in_gr = function
  | Define dn ->
     (** Probably need to fill all externally
         callable functions here **)
     add_each_in_list in_gr dn 0 do_function_name

and do_global in_gr f =
  do_function_header in_gr f

and do_compilation_unit = function
  (**  Each compilation unit have a few defines,
       type_defs, globals and function_def list **)
  | Compilation_unit (defines, type_defs, globals, fdefs) ->
     let (ds,dp,tt),in_gr =
       (** Create a top level graph that has nothing in it
           and start adding the defines to it **)
       let in_gr = get_empty_graph (7, TM.empty, MM.empty) in
       do_defines in_gr defines in
     let (ts,tp,tt),in_gr =
       (** Now add type defs **)
       add_each_in_list in_gr type_defs 0 do_type_def in
     let (g,gp,tt),in_gr =
       (** Add globals **)
       add_each_in_list in_gr globals 0 do_global in
     (** Add each function in the list **)
     let xyz,in_gr =
       add_each_in_list in_gr fdefs 0 do_function_def in
     xyz, cse_by_part in_gr

and do_type_def in_gr = function
  | Type_def(n,t) ->
     let (id_t,ii,tt),in_gr = add_sisal_type in_gr t in
     let id_,in_gr = add_sisal_typename in_gr n tt in
     ((id_t,ii,id_),in_gr)

and do_internals iin_gr f =
  let ii, in_gr = iin_gr in
  match f with
  | [] -> iin_gr
  | (Function_single (header, tdefs, nest,e))::tl ->
     print_endline ("Lowering a function header to IF1\n" ^
                      (str_function_header header));
     let (header,hp,t1),in_gr =
       do_function_header in_gr header in
     let (t,tp,_),in_gr =
       add_each_in_list in_gr tdefs 0 do_type_def in
     let _,in_gr =
       do_internals ((t,tp,t1)::ii,in_gr) nest in
     print_endline ("Lowering a function body to IF1\n" ^
                      (str_exp e));
     let jj,in_gr = match e with
       | Exp elis ->
          let olis,in_gr = add_each_in_list_to_node []
          in_gr elis 0 0 do_simple_exp in
          (olis,in_gr)
       | Empty -> [],in_gr in
     do_internals (ii@jj,in_gr) tl

and do_function_def in_gr  = function
  | Ast.Function f ->
     print_endline ("Lowering a new Function to IF1\n" ^
                      (str_function_def 2 (Ast.Function f))) ;
     let ii,in_gr_ =
       do_internals ([],get_a_new_graph in_gr) f in
     let in_gr_ = graph_clean_multiarity in_gr_ in
     let jj,kk,ll =
     try
     List.hd ii with _ ->
     raise (Sem_error ("Issue lowering function_def")) in
     let (aa,bb,cc),yyy =
       add_node_2 (
           `Compound(in_gr_,INTERNAL,ll,[],[]))
         in_gr in
     write_any_dot_file "mydot.dot" yyy;
     (aa,bb,cc),yyy
  | Forward_function f ->
     do_function_header in_gr f

and do_function_header in_gr = function
  | Function_header_nodec (fn, tl) ->
     let fn,in_gr = do_function_name in_gr fn in
     add_sisal_type in_gr (Compound_type (Sisal_function_type ("",[],tl)))
  | Function_header (Function_name fn, decls,tl) ->
     let {nmap=nm;eset=es;symtab=(cs,ps);
          typemap=yy,tm,tmn;w=i;} = in_gr in
     let nm = NM.add 0
                (let bound_node = NM.find 0 nm in
                 (match bound_node with
                  | Boundary (k,j,p) -> Boundary (k,j,(Name fn)::p)
                  | _ -> bound_node)) nm in
     let in_gr = {nmap=nm;eset=es;symtab=(cs,ps);
                  typemap=yy,tm,tmn;w=i;} in
     let tyy = extract_types_from_decl_list decls in
     let bi,(ds,_,_),in_gr =
       let rec addeach_decl in_gr decls lasti bi q =
         match decls with
         | [] -> bi,(lasti,q,0),in_gr
         | hde::tl ->
            let (lasti,pp,tt1),in_gr =
              do_params_decl lasti in_gr hde in
            addeach_decl in_gr tl lasti
              ((lasti,pp,tt1)::bi) pp in
       addeach_decl in_gr decls 0 [] [] in
     add_sisal_type in_gr (Compound_type (Sisal_function_type (fn,tyy,tl)))

let _ = do_compilation_unit
