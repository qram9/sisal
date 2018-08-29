open Ast
open If1

let in_port_1 =
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
               
(* an expression like 
   let x = 1 in sisal would
   need to return a constant
   and stick x with that Node-id *)

(** Create a compound node out of a
    function body that returns an result
    of an ADD maybe **)

(* Variable has a name and a type
   and has an associated expression *)

(* A LET EXP MAY CREATE A LOCAL SCOPE 
   IN A FOLLOWING IN EXP, SO CURRENT
   SCOPE WOULD GET PUSHED IN.
   AFTER WE ARE OUT OF THE SCOPE,
   WE MUST NOT SEE THE ELEMENTS.*)

(* We have two numbers from each recursive call:-
   one for node# and another for port#.
   Should we introduce a third one to denote type?*)

let rec zipem fst snd =
  match fst, snd with
  | hd_fst::tl_fst, hd_snd::tl_snd ->
     (*function looks generic over any list
       but it is used so far when constructing from lets.
       Triple/Double are allowed here,
       maybe they should be scalarized*)
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
        
let rec array_builder_exp in_gr = function
  | SExpr_pair(e,f) ->
     let (e,p),in_gr = do_simple_exp in_gr e in
     (match f with
      | Empty ->
         (0,0),in_gr
      | Exp fe_lis ->
         let exp_l,in_gr =
           map_exp in_gr fe_lis [] do_simple_exp in
         let (arrnum,arrport),in_gr =
           add_node_2
             (`Simple (
                  ABUILD,
                  Array.make ((List.length fe_lis)+1) "",
                  Array.make 1 "" ,[None])) in_gr in
         let in_gr = add_edge e p arrnum 0 Unknown_ty in_gr in
         let in_gr = add_each_edge exp_l arrnum 1 in_gr in
         (arrnum,arrport),in_gr)

and add_each_edge edg_lis anode nn in_gr =
  (match edg_lis with
   | (edghd,edgp)::edgtl ->
      add_each_edge edgtl anode (nn+1)
        (add_edge edghd edgp anode nn Unknown_ty in_gr)
   | [] -> in_gr)
  
and do_each_exp_in_strm in_gr = function
  | (hdn,hdp)::tll ->
     let (i,j),in_gr = do_each_exp_in_strm in_gr tll in
     let (k,l),in_gr = add_node_2 (`Simple
                                     (SAPPEND,
                                      Array.make 2 "",
                                      Array.make 1"",
                                      [None])) in_gr in
     (k,l),(add_edge hdn hdp k 0 Unknown_ty (add_edge i j k 1 Unknown_ty in_gr))
     
  | [] ->
     add_node_2 (`Simple
                   (SBUILD,
                    Array.make 1 "",
                    Array.make 1 "",[None])) in_gr

and record_builder in_gr fdl =
  let rec record_builder_impl (aa,in_gr) = function
    | Field_def(fn,ex1)::tl ->
       let fn = do_field_name in_gr fn in
       let exp_l,in_gr =
         do_simple_exp in_gr ex1 in
       record_builder_impl (exp_l::aa,in_gr) tl    
    | [] -> aa,in_gr in
  let lll,in_gr = record_builder_impl ([],in_gr) fdl in
  let (bb,pp),in_gr =
    add_node_2(`Simple(RBUILD,Array.make ((List.length fdl)+1) "",
                       Array.make 1 "",[None])) in_gr in
  let in_gr = add_each_edge lll bb 0 in_gr in
  (bb,pp),in_gr

and add_edges_in_list exp_list anode portnum in_gr =
  match exp_list with
  | (hd_node,in_port)::tl ->
     add_edges_in_list
       tl
       anode
       (portnum+1)
       (add_edge hd_node in_port
          anode portnum Unknown_ty in_gr)
  | [] -> ((anode,0),in_gr)     

and do_tagnames in_gr = function
  | Tagnames tn -> ((0,0), in_gr)

and do_direction in_gr = function
  | No_dir -> ((0,0), in_gr)
  | Left -> ((0,0), in_gr)
  | Right -> ((0,0), in_gr)
  | Tree -> ((0,0), in_gr)

and do_reduction in_gr = function
  | Sum -> ((0,0), in_gr)
  | Product -> ((0,0), in_gr)
  | Least -> ((0,0), in_gr)
  | Greatest -> ((0,0), in_gr)
  | Catenate -> ((0,0), in_gr)
  | No_red -> ((0,0), in_gr)

and do_return_exp in_gr = function
  | Value_of (d,r,e) ->
     let (direc,dp),in_gr = do_direction in_gr d in
     let (reduc,rp),in_gr = do_reduction in_gr r in
     do_exp in_gr e
  | Array_of e ->
     do_exp in_gr e
  | Stream_of e ->
     do_exp in_gr e

and do_masking_clause in_gr = function
  | Unless e ->
     do_exp in_gr e
  | When e ->
     do_exp in_gr e
  | No_mask ->
     ((0,0), in_gr)

and do_iterator in_gr = function
  | Repeat dp ->
     do_decldef_part in_gr dp

and do_termination in_gr = function
  | While e ->
     do_exp in_gr e
  | Until e ->
     do_exp in_gr e

and do_return_clause in_gr = function
  | Old_ret (re, mc) ->
     let (re,iii),in_gr =
       do_return_exp
         in_gr re in
     do_masking_clause in_gr mc
  | Return_exp (re,mc) ->
     let (re,iii),in_gr = do_return_exp in_gr re in
     do_masking_clause in_gr mc

and do_taglist in_gr = function
  | Tag_list (tns,e) ->
     let (tns,iii),in_gr = do_tagnames in_gr tns in
     do_exp in_gr e

and do_taglist_list in_gr tls =
  add_each_in_list in_gr tls 0 do_taglist

and do_tagcase_exp in_gr = function
  | Assign(vn,e) ->
     let (vn,vp),in_gr = do_val in_gr vn in
     do_exp in_gr e
  | Tagcase_exp (exp) ->
     do_exp in_gr exp

and do_otherwise in_gr = function
  | Otherwise e ->
     do_exp in_gr e

and do_constant in_gr xx =
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

and do_val in_gr = function
  | Value_name v ->
     match in_gr with
       {
         nmap=nmap;
         eset=eset;
         symtab = (umap,vma);
         typemap=oo,tm,tmn;
         w=w
       } ->
       get_symbol_id v in_gr

and do_exp in_gr = function
  | Exp e ->
     add_each_in_list in_gr e 0 do_simple_exp
  | Empty -> ((0,0), in_gr)

and do_exp_pair in_gr = function
  | Expr_pair (e,f) ->
     let (e,p),in_gr = do_exp in_gr e in do_exp in_gr f

and do_field_name in_gr = function
  | Field_name f -> let f = f in ((0,0), in_gr)

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

and do_cond in_gr = function
  | Cond (c,e) ->
     let _,in_gr = do_exp in_gr c in
     do_exp in_gr e

and do_in_exp in_gr = function
  | In_exp (vn,e) ->
     let vn = do_val in_gr vn in
     do_exp in_gr e
  | At_exp (ie,vn) ->
     let _,in_gr = do_in_exp in_gr ie in
     do_val in_gr vn
  | Dot (ie1, ie2) ->
     let _,in_gr = do_in_exp in_gr ie1 in
     do_in_exp in_gr ie2
  | Cross (ie1,ie2) ->
     let _,in_gr = do_in_exp in_gr ie1 in
     do_in_exp in_gr ie2

and do_if in_gr f =
  add_each_in_list in_gr f 0 do_cond

and do_else in_gr = function
  | Else e -> do_exp in_gr e

and do_tag_exp in_gr = function
  | Tag_name tn ->
     let tn = tn in ((0,0), in_gr)
  | Tag_exp (tn, ex) ->
     let tn = tn in
     do_exp in_gr ex

and do_prefix_name in_gr = function
  | Char_prefix -> ((0,0), in_gr)
  | Double_prefix -> ((0,0), in_gr)
  | Integer_prefix -> ((0,0), in_gr)
  | Real_prefix -> ((0,0), in_gr)

and do_decldef_part in_gr = function
  | Decldef_part f ->
     add_each_in_list in_gr f 0 do_decldef

and do_def in_gr = function
  | Def (x1,y) ->
     let named_exp = match y with
       | Exp ee -> zipem x1 ee
       | _ -> [] in
     let rec add_all_to_sm
               ((nx,po),
                {
                  nmap=nmap;
                  eset=eset;
                  symtab=(umap,vmap);
                  typemap=tm;
                  w=w
               }) xli =
       match xli with
       | [] ->
          ((0,0),
           {
             nmap=nmap;
             eset=eset;
             symtab=(umap,vmap);
             typemap=tm;
             w=w
          })
       | (hdx,ee)::tlx ->
          let (nx,po),
              {
                nmap=nmap;
                eset=eset;
                symtab=(umap,vmap);
                typemap=tm;
                w=w
              } =
            do_simple_exp
              {
                nmap=nmap;
                eset=eset;
                symtab=(umap,vmap);
                typemap=tm;   
                w=w
              } ee in
          (let existing_rec = SM.find hdx umap in
           match existing_rec
           with {val_name=hdx;
                 val_ty=aty;
                 val_def=_} ->
                 add_all_to_sm
                   ((nx,po),
                    {
                      nmap=nmap;
                      eset=eset;
                      symtab=(SM.add hdx
                                {val_name=hdx;val_ty=aty;val_def=nx} umap,
                              vmap);
                      typemap=tm;
                      w=w
                    }
                   )
                   tlx
              | _ -> raise
                       (Node_not_found
                          "Unknown symtab entry")) in
     add_all_to_sm ((0,0),in_gr) named_exp

and do_decl in_gr = function
  | Decl(x,y) ->
     let ((type_num,_),in_gr) =
       add_sisal_type in_gr y in
     match in_gr with
     | {
         nmap=nmap;
         eset=eset;
         symtab=(u,v);
         typemap=tm;
         w=w
       } ->
        let rec add_all_to_sm umap xli =
          match xli with
          | hdx::tlx ->
             let sm_v =
               {
                 val_name=hdx;
                 val_ty=type_num;
                 val_def=0
               } in
             add_all_to_sm (SM.add hdx sm_v umap) tlx
          | [] -> umap in
        let u = add_all_to_sm u x in
        ((0,0),
         {
           nmap=nmap;
           eset=eset;
           symtab=(u,v);
           typemap=tm;
           w=w
        })

and do_decl_helper in_gr ex1 xl =
  match in_gr with
  | {
      nmap=nmap;
      eset=eset;
      symtab=(umap,v);
      typemap=tm;
      w=w
    } ->
     let umap =
       let existing_rec = SM.find xl umap in
       match existing_rec
       with {
           val_name=xl;
           val_ty=aty;
           val_def=_
         } ->
         (SM.add xl
            {
              val_name=xl;
              val_ty=aty;
              val_def=ex1
            } umap)
     in umap

and do_decldef in_gr =
  let in_gr = unify_syms in_gr in
  function
  | Decl_def x ->
     do_def in_gr x
  | Decl_decl x ->
     do_decl in_gr x
  | Decldef (x,y) ->
     (* this goes inside out *)
     let rec name_list xx =
       match xx with
         Decl(xxh,xxy)::tlx -> xxh @(name_list tlx)
        |[] -> [] in
     let named_exp = match y with
       | Exp ee ->
          zipem (name_list x) ee
       | _ -> [] in
     let rec add_decl_exp xlis in_gr =
       match xlis with
         (x,ey)::tl ->
          let (num_node,po), in_gr =
            do_simple_exp in_gr ey in
          (match in_gr with
           | {
               nmap=nb;
               eset=eb;
               symtab=(u,v);
               typemap=tm;
               w=w
             } ->          
              add_decl_exp tl
                (
                  {
                    nmap=nb;
                    eset=eb;
                    symtab=(do_decl_helper in_gr num_node x, v);
                    typemap=tm;
                    w=w
                  }
                )
          )
       | [] -> in_gr in
     let (_,_),in_gr =
       add_each_in_list in_gr x 0 do_decl in
     let ret_val =
       ((0,0),add_decl_exp named_exp in_gr)
     in ret_val

and do_function_name in_gr = function
  | Function_name f ->
     let f = f in
     ((0,0), in_gr)

and do_arg in_gr = function
  | Arg e -> do_exp in_gr e

and do_simple_exp in_gr in_sim_ex =
  let bin_fun a b in_gr node_tag =
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
      (let (c,pi1),i_gr =
         do_simple_exp in_gr a in
       let (d,pi2),i_gr =
         do_simple_exp i_gr b in
       let (z,_), out_gr =
         get_simple_bin i_gr node_tag in
       let out_gr =
         add_edge c pi1 z 0 Unknown_ty out_gr in
       let out_gr =
         add_edge d pi2 z 1 Unknown_ty out_gr in
       ((z,0),out_gr)) in
    match (a,b) with
    | (Constant ax),(Constant ay) ->
       let (z,_),
           {nmap=nm;
            eset=es;
            symtab=ss;
            typemap=tm;
            w=i} =
         get_simple_bin in_gr node_tag in
       let anod1 = NM.find z nm in
       let anod1 = set_in_port_str anod1 0
                     ("\"" ^ (Ast.str_constant ax) ^ "\"") in
       let anod1 = set_in_port_str anod1 1
                     ("\"" ^ (Ast.str_constant ay) ^ "\"") in
       (z,0),{nmap=NM.add z anod1 nm;
              eset=es;
              symtab=ss;
              typemap=tm;
              w=i}
    | (Constant ax), (_ as ay) ->
       let (z,_),i_gr =
         get_simple_bin in_gr node_tag in
       let {nmap=nm;
            eset=es;
            symtab=ss;
            typemap=tm;
            w=i} = i_gr in       
       let anod1 = NM.find z nm in
       let anod1 = set_in_port_str anod1 0
                     ("\"" ^ (Ast.str_constant ax) ^ "\"") in
       let {nmap=nm;
            eset=es;
            symtab=ss;
            typemap=tm;
            w=i} = i_gr in       
       let (d,pi2),i_gr =
         do_simple_exp i_gr ay in
       let {nmap=nm;
            eset=es;
            symtab=ss;
            typemap=tm;
            w=i} = 
         add_edge d pi2 z 1 Unknown_ty i_gr in       
       (z,0),{nmap=NM.add z anod1 nm;
              eset=es;
              symtab=ss;
              typemap=tm;
              w=i}                     
    | (_ as ax), (Constant ay) ->
       let (z,_),in_gr =
         get_simple_bin in_gr node_tag in
       let {nmap=nm;
            eset=es;
            symtab=ss;
            typemap=tm;
            w=i} = in_gr in       
       let anod1 = NM.find z nm in
       let (c,pi1), in_gr =
         do_simple_exp in_gr ax in
       let {nmap=nm;
            eset=es;
            symtab=ss;
            typemap=tm;
            w=i} =
         add_edge c pi1 z 0 Unknown_ty in_gr in
       let anod1 = set_in_port_str anod1 1
                     ("\"" ^ (Ast.str_constant ay) ^ "\"") in
       (z,0),{nmap=NM.add z anod1 nm;
              eset=es;
              symtab=ss;
              typemap=tm;
              w=i}
    | _ ->
       base_case_bin a b node_tag in_gr in
  let unary_fun in_gr e node_tag =
    let get_simple_unary in_gr node_tag =
      let in_port_1 =
        let in_array = Array.make 1 "" in
        in_array in
      let out_port_1 =
        let out_array = Array.make 1 "" in
        out_array in   
      let (z,_),in_gr =
        add_node_2 (
            `Simple
              (node_tag,in_port_1,out_port_1,[None])) in_gr in
      ((z,0), in_gr) in
    (match e with
     | Constant x ->
        let (z,_),
            {nmap=nm;
             eset=es;
             symtab=ss;
             typemap=tm;
             w=i} = get_simple_unary in_gr node_tag in
        let anod1 = NM.find z nm in
        let anod1 = set_in_port_str anod1 0
                      ("\"" ^ (Ast.str_constant x) ^ "\"") in
        (z,0),{nmap = NM.add z anod1 nm;eset=es;symtab=ss;typemap=tm;w=i}
     | _ -> 
        let (e,pi),in_gr = do_simple_exp in_gr e in
        let (z,_), in_gr = get_simple_unary in_gr node_tag in
        let in_gr = add_edge e pi z 0 Unknown_ty in_gr in
        ((z,0),in_gr)) in
  match in_sim_ex with
  | Constant x -> do_constant in_gr x
  | Not e -> unary_fun in_gr e NOT
  | Negate e -> unary_fun in_gr e NEGATE
  | Pipe (a,b) -> bin_fun a b in_gr ACATENATE
  | And (a,b) ->  bin_fun a b in_gr AND
  | Divide (a,b) -> bin_fun a b in_gr DIVIDE     
  | Multiply (a,b) -> bin_fun a b in_gr MULTIPLY
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
         let ((n,k),in_gr) =
           add_node_2
             (`Simple (INVOCATION, in_port_00,
                       out_port_0, prags))
             in_gr in
         add_edges_in_list expl n 0 in_gr)
    
  | Array_ref (ar_a,ar_b) ->
     let (arr_node,arr_port),in_gr =
       do_simple_exp in_gr ar_a in
     let (res_node,res_port),in_gr_res =
       (match ar_b with
        | Exp ex_lis ->
           let add_basic_arr_elem arr_indx
                 ((aaa,bbb),in_gr) =
             let (idxnum,idxport),in_gr1 =
               do_simple_exp in_gr arr_indx in
             let (arrnum,arrport),in_gr2 =
               add_node_2
                 (`Simple (AELEMENT,Array.make 2 "",Array.make 1 "",[]))
                 in_gr1 in
             ((arrnum,arrport),
              add_edge aaa bbb arrnum 0 Unknown_ty
                (add_edge idxnum idxport
                   arrnum 1 Unknown_ty in_gr2)) in
           List.fold_right add_basic_arr_elem
             ex_lis ((arr_node,arr_port),in_gr)
        | _ -> ((arr_node,arr_port),in_gr))
     in ((res_node,res_port),in_gr_res)
      
  | Let (dp,e) ->
     let x,in_gr = do_decldef_part in_gr dp in
     do_exp in_gr e
     
  | Old v -> do_val in_gr v
  | Val v -> do_val in_gr v
  | Paren e -> do_exp in_gr e
             
  | Array_generator_named tn ->
     let tn = tn in (0,0),in_gr
  | Array_generator_named_addr (tn,ep) ->
     let tn = tn in
     array_builder_exp in_gr ep
  | Array_generator_unnamed ep ->
     array_builder_exp in_gr ep
    
  | Array_replace (p,epl) ->
     let (sn,sp),in_gr = do_simple_exp in_gr p in
     let rec do_array_replace ((sn,sp),in_gr) =
       function
       | SExpr_pair (idx,values)::tl ->
          let (al,ap),in_gr =
            (match values with
             | Empty ->
                raise (Node_not_found
                         "badly formed array replace")
             | Exp aexp ->
                let bbu,in_gr =
                  map_exp in_gr aexp [] do_simple_exp in
                let (idxnum,idxport),in_gr =
                  do_simple_exp in_gr idx in
                let (bb,pp),in_gr =
                  add_node_2
                    (`Simple(
                         AREPLACE,
                         (Array.make ((List.length aexp)+2) ""),
                         Array.make 1 "",[]))
                    in_gr in
                let in_gr =
                  add_edge idxnum idxport bb 1 Unknown_ty
                    (add_edge sn sp bb 0 Unknown_ty in_gr) in
                add_edges_in_list bbu bb 2 in_gr) in
          let (tan,tap),in_gr =
            do_array_replace ((al,ap),in_gr) tl
          in (tan,tap),in_gr
       | [] -> (sn,sp),in_gr in
     do_array_replace ((sn,sp),in_gr) epl

  | Record_ref (e,fn) ->
     let fn = match fn with
       | Field_name fn -> fn in
     let (ain,apo),in_gr = do_simple_exp in_gr e in
     let (bb,pp),in_gr =
       let in_porst = Array.make 2 "" in
       in_porst.(0) <- fn;
       add_node_2 (`Simple(
                       RELEMENTS,in_porst,
                       Array.make 1 "",[None])) in_gr in
     (bb,pp),(add_edge ain apo bb 1 Unknown_ty in_gr)

  | Record_generator_primary (e,fdle) ->
     let (e,p),in_gr = do_simple_exp in_gr e in
     let rec do_each_field ((a,b),in_gr) = function
       | Field_exp (Field fi,se)::tl ->
          let (aseb,asep),in_gr = do_simple_exp in_gr se in
          let rec do_field_chain ((fe,ff),in_gr) = function
            | (Field_name fna)::tll ->
               let (bb,bp),in_gr =
                 let in_porst = Array.make 3 "" in
                 in_porst.(1) <- fna;
                 let (bb,bp),in_gr =
                   add_node_2 (
                       `Simple (
                           RREPLACE,
                           in_porst,
                           Array.make 1 "",[None])) in_gr in
                 (bb,bp),add_edge fe ff bb 0 Unknown_ty in_gr in
               do_field_chain ((bb,bp),in_gr) tll
            | [] -> (fe,ff),add_edge aseb asep fe 2 Unknown_ty in_gr in
          do_each_field (do_field_chain ((a,b),in_gr) fi) tl
       | [] -> (a,b),in_gr in
     do_each_field ((e,p),in_gr) fdle

  | Record_generator_unnamed (fdl) ->
     record_builder in_gr fdl

  | Record_generator_named (tn,fdl) ->
     (*we can look up tn against the known types.
       Following that we may have to thread in
       the record type to the builder to check that the
       return types are correct. *)
     let tn = tn in
     record_builder in_gr fdl

  | Stream_generator tn ->
     let tn = tn in
     add_node_2 (`Simple (SBUILD,
                          Array.make 1 "",
                          Array.make 1 "",
                          [None])) in_gr

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
    
  | Is (tn,e) -> 
     let tn = tn in
     do_exp in_gr e
  | Union_generator (tn,te) ->
     let tn = tn in
     do_tag_exp in_gr te
  | Prefix_operation (pn,e) ->
     let (n,p),in_gr = do_prefix_name in_gr pn in
     do_exp in_gr e
  | Is_error e ->
     do_exp in_gr e
  | Tagcase (ae,tc,o) ->
     let (a,ap),in_gr = do_tagcase_exp in_gr ae in
     let (t,tp),in_gr = do_taglist_list in_gr tc in
     do_otherwise in_gr o
  | If (cl, el) ->
     let (c,p),in_gr = do_if in_gr cl in
     do_else in_gr el
  | For_all (i,d,r) ->
     let (i,p),in_gr = do_in_exp in_gr i in
     let (d,q),in_gr = do_decldef_part in_gr d in
     add_each_in_list in_gr r 0 do_return_clause
  | For_initial (d,i,r) -> 
     let loopAOrB i in_gr = match i with 
       | Iterator_termination (ii,t) ->
          let (ii,ip),in_gr = do_iterator in_gr ii in
          let (t,tp),in_gr = do_termination in_gr t in
          let (r,rp),in_gr =
            add_each_in_list in_gr r 0 do_return_clause in
          do_decldef_part in_gr d
       | Termination_iterator (t,ii) ->
          let d = do_decldef_part in_gr d in
          let t = do_termination in_gr t in
          let ii = do_iterator in_gr ii in
          add_each_in_list in_gr r 0 do_return_clause in
     loopAOrB i in_gr

and do_type_list in_gr tl =
  add_each_in_list in_gr tl 0 add_sisal_type

and do_defines in_gr = function
  | Define dn ->
     add_each_in_list in_gr dn 0 do_function_name

and do_global in_gr f =
  do_function_header in_gr f

and do_compilation_unit = function
  | Compilation_unit (defines, type_defs, globals, fdefs) ->
     let (ds,dp),in_gr =
       let in_gr = get_empty_graph in 
       do_defines in_gr defines in
     let (ts,tp),in_gr =
       add_each_in_list in_gr type_defs 0 do_type_def in
     let (g,gp),in_gr =
       add_each_in_list in_gr globals 0 do_global in
     add_each_in_list in_gr fdefs 0 do_function_def

and do_type_def in_gr = function
  | Type_def(n,t) ->
     let (id_t,ii),in_gr =
       add_sisal_type in_gr t in
     let id_,in_gr = add_sisal_typename in_gr n in
     ((id_t,ii),in_gr)

and do_internals iin_gr f =
  let ii, in_gr = iin_gr in
  let si = string_of_graph in_gr in
  match f with
  | [] ->
     iin_gr
  | (Function_single (header, tdefs, nest,e))::tl ->
     let (header,hp),in_gr =
       do_function_header in_gr header in
     let (t,tp),in_gr =
       add_each_in_list in_gr tdefs 0 do_type_def in
     let _,in_gr =
       do_internals ((t,tp)::ii,in_gr) nest in
     let (a,ap),in_gr = do_exp in_gr e in
     let gg = string_of_graph in_gr in
     do_internals ((a,ap)::ii,in_gr) tl

and do_function_def in_gr  = function
  | Ast.Function f ->
     let ii,{nmap =  nm;
             eset = es;
             symtab = (cs,ps);
             typemap = yy,tm,tmn;
             w = i;} =
       do_internals ([],get_empty_graph) f in
     let in_gr_ =
       {nmap =  nm;
        eset = es;
        symtab = (cs,ps);
        typemap = yy,tm,tmn;
        w = i;} in
     let yyy = update_boundary_link ii in_gr_
                 (NM.find 0 nm) in
     let _, yyy = add_node_2 (`Compound(yyy,[],[]))
                    in_gr in
     ((0,0),yyy)
  | Forward_function f ->
     do_function_header in_gr f

and do_function_header in_gr = function
  | Function_header_nodec (fn, tl) ->
     let fn,in_gr = do_function_name in_gr fn in
     do_type_list in_gr tl
  | Function_header (Function_name fn, decls,tl) ->
     let (_,_),in_gr =
       do_function_name in_gr (Function_name fn) in
     let {nmap=nm;
          eset=es;
          symtab=(cs,ps);
          typemap=yy,tm,tmn;
          w=i;} = in_gr in
     let nm = NM.add 0
                (let bound_node =
                   NM.find 0 nm in
                 (match bound_node with
                  | Boundary (r,j,p) ->
                     Boundary (r,j,(Name fn)::p)
                  | _ -> bound_node)) nm in
     let in_gr = {nmap=nm;
                  eset=es;
                  symtab=(cs,ps);
                  typemap=yy,tm,tmn;
                  w=i;} in
     let (ds,dp),in_gr =
       add_each_in_list in_gr decls 0 do_decl in
     do_type_list in_gr tl
let _ = do_compilation_unit
