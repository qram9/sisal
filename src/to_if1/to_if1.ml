(*TODO:

  1: Dot-files must be more descriptive.
  2: Need to provide a debug-msging mechanism
   for each pass- like CSE for instance.
  3: Each visitor could have a debug flag
   that it passes to its callees - not sure
   how we may have this. Perhaps a Graph entry.
  4: BUNCH OF CASES FAIL DUE TO TYPE MISMATCH,
   MAYBE SOMETHING TRIVIAL. NEED TO ALSO SEE IF
   THE NESTED FUNCTIONS CAPTURE ANY VARS FROM
   OUTSIDE AND NEED TO SEE HOW THAT WOULD BE
   SUPPORTED.. MIGHT BE SOMETHING TO CONFIRM
   WITH THE STANDARD.
  5: TODO -> SEEMS LIKE WHEN WE HAVE A DECL WITH
   MULTIPLE TYPES, ALL TYPES SEEM TO TAKE THE FIRST
   TYPE ALL THE TIME.
*)

(* TEST about multiple definition to same variable in a scope,
   add scope numbers, level etc. *)
(* Can we add array dope-vectors *)
(* TO_TEST: inputs to select do not seem to get from outer scope *)
(* TODO: forall do not seem to pull inputs from outside *)
(* many boundary boxes are empty *)
(* TODO (15july2019): Most compiler warnings that remain in this file are
   in the tagcase/If1.union lowering. *)
(** Ideas here mostly come from the single paper: "IF1, AN INTERMEDIATE FORM FOR
    APPLICATIVE LANGUAGES, JULY 31, 1985 VERSION 1.0".

    This is also useful: "FRONTEND OF A SISAL COMPILER, RIYAZ V.P, M.TECH THESIS
    INDIAN INST OF TECH. KANPUR, MARCH 1993". *)

(** IF1 is a dataflow graph format generated with some effort (boring and time
    consuming) using an AST visitor/walker for the applicative and single
    assignment SISAL langauge. The language has let bindings, compound
    statements like forall (perfect loops with scoping similar to nested lets,
    with mostly bindings similar to a standard let), for_initial, if expressions
    (select expressions), tagged unions which are mostly like ML variants but
    with one difference - sharing of the body expression by different tags is
    allowed, nested functions but no higher order functions (though, SISAL2 and
    SISAL90 support higher order functions). Types would need to be provided by
    the user, for the most part, with an exception for arithmetic operations,
    for which the compiler infers types from the expression's operands. When
    types are specified, infered types need to be checked against the specified
    types etc. LET's are lowered here using hierarchical symtabs, with a parent
    If1.symtab for enclosing-scope and one for current-scope.

    Each lowering function below should start with a do_, for example, do_exp,
    do_simple_exp etc. Their purpose would be to recursively lower an incoming
    AST type (for the two mentioned above, exp, simple_exp would be the AST
    type) to IF1. The return value is a quadruple, organized into a triplet of
    ints followed by a graph type: (x, y, z), gr :- x signifying node-id, y for
    port-id and z for type-id, and finally gr is a graph type that you may find
    in if1.ml. The difficulty here is that we just return only one int as the
    producing node's ID. But AST types may return multiple values. Any function
    could return many values; or and parallel assignments are possible as well.
    What I did was introduce a If1.MULTIARITY node, which has enough incoming
    ports for each result values, and now we can get away with the single ID
    that of the If1.MULTIARITY node. The users get a MULTIARITY and then connect
    to the input ports of the MULTIARITY directly. Thus MULTIARITY is just an
    indirection and is thrown away when returning to the Callee.

    A spate of library functions do exist... DOUBLE, TRIPLE are some shortcuts
    to create tuples from expressions or declarations. There are peculiarities
    in function declarations due to the need for forward declarations etc.

    In modern day Graphics languages like openGL/CL etc and with CPU/GPU
    vector-instruction support, we often find intrinsic based code. Thus I added
    a series of vector and matrix types based off OpenCL/GL - they should be
    directly mappable to vector swizzles and mat-vec multiplies seen in graphics
    circles and give us ability to write OpenGL like swizzle code. Also these
    data-types should map to most processor's vector SIMD registers.

    In one of the kinds of loops called the FOR INITIAL loop, there is a keyword
    called Old. This takes some explanation. The statements in the FOR INITIAL
    or FOR loops are written like C assignments. These statements are called
    DeclDefs. A decldef looks like X := some expn; Each of these statements are
    basically the same as a let statement, like let name = expn in expn in ML
    like languages. So we need to imagine an imaginary let before the
    statement's LHS and an 'in' to replace the ';' ending the decldef. Now if we
    have an exp i = i + 1; k = i; in a loop, the meaning is akin to Ml lang
    statement: let i = i + 1 in k = i.

    With a redefinition of any name it would now be shadowed and the old binding
    is no longer available. Thus after that statement, the previous loop's value
    is not available. I suppose we could make a copy of it with a new name with
    a decldef at the beginning of the loop. Thus, I guess the hacky 'Old i' came
    about to be able to refer to the earlier iteration's value, wherever
    required in all of the current iteration's decldefs.

    I guess only from the last iteration and not two or more iterations ago -
    like we would have in a reduction. That can be written as well using this
    old i trick and some extra variables, maybe. In any case I cannot fully
    understand why they needed this 'Old'.

    Old is only available for "FOR INITIAL" loops, which are basically like tail
    recursive function calls. In contrast, the "FOR" loop is a fully parallel
    loop. But the body is still a nested let-in written with decldefs. I suppose
    we could do t3 := old t2; t2 := old t1; k := t3 + t2; t1 := t1 + 1; but we
    could do that without the old keyword.

    We often find that there are some let's mixed in the loops to make some LHS
    value usable in an if-else compound statement and the code could get
    confusing as a result. The If-else body or condition would need to be an
    expression and not decldefs.

    The semicolon everywhere in the language is to be treated like that. It is
    not equivalent to Ocaml's "and" for parallel copies. We would probably like
    to have an "and" to add a parallel decldef list. That is an easy addition.

    Recursions and cross recursions are easy as the only thing required is a
    forward declaration. However to handle Higher Order Functions we would need
    to add a Rec keyword like ML; otherwise the LHS name in the decldef is not
    going to be made available to the RHS, just like in ML like langs.

    What next: 1: I also found reading Prof. Andrew Appel's book: "Compiling
    with Continuations" facinating-- including callcc etc concepts. CPS callcc
    etc. Every compiler stage is discussed and also they discuss closure
    conversion etc. and maybe a CPS lowering would be fun to do...

    2: For better usability: SISAL2 etc had written about but not attempted...*)

module Ast = Ir.Ast
module If1 = Ir.If1
module Slurper = Utils.Slurper

let to_if1_msg lvl fmt = Ir.Debug.msg "to_if1" lvl fmt

module StructMap = Map.Make (struct
  type t = If1.if1_ty

  let compare = compare
end)

(*
let str_type_trace () =
  let buf = Buffer.create 1024 in
  List.iter (fun (id, name, trace) ->
    Printf.bprintf buf "id %d Name %s Trace:\n%s\n" id name trace
  ) (List.rev !type_trace);
  Buffer.contents buf *)

let dbg_trace : string ref = ref ""
let current_src_pos : (int * int) ref = ref (0, 0)

let in_port_1 =
  (* memory allocate arrays *)
  let in_array = Array.make 2 "" in
  in_array.(0) <- "0";
  in_array

let in_port_2 =
  let in_array = Array.make 2 "" in
  in_array.(0) <- "0";
  in_array.(1) <- "1";
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
   and set x with that Node-id **)

(* Variable has a name and a type
   and has an associated expression **)

(*A LET EXP MAY CREATE A LOCAL SCOPE
   IN A FOLLOWING IN EXP, SO CURRENT
   SCOPE WOULD GET PUSHED IN.
   AFTER WE ARE OUT OF THE SCOPE,
   WE WILL NOT SEE THE ELEMENTS.**)

(* We have three numbers returned from
    each recursive call:-
    One for node#, one for port# and one for type#.*)

let rec zipem fst snd =
  (* Add a pair of elements to a list, from
      two input lists *)
  match (fst, snd) with
  | hd_fst :: tl_fst, hd_snd :: tl_snd ->
      (* function looks generic over any list
        but it is used so far when constructing from lets.
        Triple/Double are allowed here,
        maybe they should be scalarized **)
      (hd_fst, hd_snd) :: zipem tl_fst tl_snd
  | _, _ -> []

let rec string_of_zip zipped fst_fn snd_fn =
  match zipped with
  | (hd_fst, hd_snd) :: tl_fst ->
      (*Triple/Double are allowed here*)
      "(" ^ fst_fn hd_fst ^ "," ^ snd_fn hd_snd ^ ")"
      ^ string_of_zip tl_fst fst_fn snd_fn
  | [] -> ""

let rec array_builder_exp ?(inc_typ = 0) in_gr = function
  (* Helper function that code generates
      IF1 tree for building arrays *)
  | Ast.SExpr_pair (e, f) -> (
      let (e, p, t1), in_gr = do_exp in_gr e in
      match f with
      | Ast.Empty -> ((0, 0, 0), in_gr)
      | Ast.Exp fe_lis ->
          let exp_l, in_gr = If1.map_exp in_gr fe_lis [] do_simple_exp in
          let (arrnum, arrport, _), in_gr =
            If1.add_node_2
              (`Simple
                 ( If1.ABUILD,
                   Array.make (List.length fe_lis + 1) "",
                   Array.make 1 "",
                   [ If1.No_pragma ] ))
              in_gr
          in
          let in_gr = If1.add_edge e p arrnum 0 t1 in_gr in
          let in_gr = add_each_edge exp_l arrnum 1 in_gr in
          let t1, in_gr =
            let nn, pp, ofty =
              assert (List.length exp_l <> 0);
              List.hd exp_l
            in
            (* Resolve type through MULTIARITY nodes (e.g. for-loop results) *)
            let _, _, ofty =
              if ofty = 0 then
                If1.find_incoming_regular_node (nn, pp, ofty) in_gr
              else (nn, pp, ofty)
            in
            if inc_typ = 0 then
              let (id, _, _), in_gr =
                If1.add_type_to_typemap_dedup (If1.Array_ty ofty) in_gr
              in
              (id, in_gr)
            else
              (* inc_typ is a named type: if it's already an array type
                 (e.g. `ARRAY AR [...]` where AR = ARRAY[INTEGER]), use it
                 directly.  If it's a non-array type (e.g. a function type),
                 treat it as the element type and build array[inc_typ]. *)
              if If1.is_array_type inc_typ in_gr then (inc_typ, in_gr)
              else
                let (id, _, _), in_gr =
                  If1.add_type_to_typemap_dedup (If1.Array_ty inc_typ) in_gr
                in
                (id, in_gr)
          in
          ((arrnum, arrport, t1), in_gr))

and add_each_edge edg_lis tail_node nn in_gr =
  (* Call If1.add_edge for a list, connected
      to tail_node, starting at port nn*)
  match edg_lis with
  | (edghd, edgp, tty) :: edgtl ->
      add_each_edge edgtl tail_node (nn + 1)
        (If1.add_edge edghd edgp tail_node nn tty in_gr)
  | [] -> in_gr

and add_edges_for_fields edg_lis tail_node nn in_gr =
  (* Minor variant of above function, add_each_edge *)
  match edg_lis with
  | (_, (edghd, edgp, tty)) :: edgtl ->
      add_edges_for_fields edgtl tail_node (nn + 1)
        (If1.add_edge edghd edgp tail_node nn tty in_gr)
  | [] -> in_gr

and do_each_exp_in_strm in_gr = function
  (* Helper function for stream SAPPEND expression.
     Builds right-to-left: SBUILD <- SAPPEND(e_last) <- SAPPEND(e_{n-1}) <- ... *)
  | (hdn, hdp, elt_ty) :: tll ->
      let (i, j, strm_ty), in_gr = do_each_exp_in_strm in_gr tll in
      (* strm_ty is the stream type from the recursive call; recover element type
         from the stream type if strm_ty is already a Stream, else derive it *)
      let elt_ty, strm_ty, in_gr =
        if strm_ty = 0 then
          (* base case returned SBUILD with type 0; create Stream type now *)
          let (stream_id, _, _), in_gr =
            If1.add_type_to_typemap_dedup (If1.Stream elt_ty) in_gr
          in
          (elt_ty, stream_id, in_gr)
        else
          (* already have a stream type; recover element type from it *)
          let elem_ty =
            match If1.lookup_ty strm_ty in_gr with
            | If1.Stream e -> e
            | _ -> elt_ty
          in
          (elem_ty, strm_ty, in_gr)
      in
      let (k, l, _), in_gr =
        If1.add_node_2
          (`Simple
             (If1.SAPPEND, Array.make 2 "", Array.make 1 "", [ If1.No_pragma ]))
          in_gr
      in
      ( (k, l, strm_ty),
        If1.add_edge hdn hdp k 0 elt_ty (If1.add_edge i j k 1 strm_ty in_gr) )
  | [] ->
      If1.add_node_2
        (`Simple
           (If1.SBUILD, Array.make 1 "", Array.make 1 "", [ If1.No_pragma ]))
        in_gr

and get_tys ttts ous =
  (* Types are extracted from a
      triplet and added to a list *)
  match ttts with
  | (fn, (_, _, tt)) :: tl -> get_tys tl ((fn, tt) :: ous)
  | [] -> ous

and union_builder in_gr utags iornone =
  (* If1.Union or If1.Record builder helper function *)
  let union_builder_impl in_gr = function
    | Ast.Tag_exp (tn, ex1) ->
        let exp_l, in_gr = do_simple_exp in_gr ex1 in
        ((tn, exp_l), in_gr)
    | _ -> raise (If1.Sem_error "Internal compiler error")
  in
  let lll, in_gr = union_builder_impl in_gr utags in
  let tm = If1.get_typemap_tm in_gr in
  let hdty =
    If1.TM.fold
      (fun k v z ->
        match z with
        | If1.Emp -> (
            let bar xx lt = match (xx, lt) with _, _ -> If1.Som k in
            match v with If1.Union (lt, _, xx) -> bar xx lt | _ -> z)
        | _ -> z)
      tm If1.Emp
  in
  let hdty =
    match hdty with
    | If1.Som _ -> hdty
    | If1.Emp -> failwith "unknown field in an If1.union"
  in
  let aout =
    match iornone with
    | If1.Emp -> (
        let eee = match hdty with If1.Som x -> x | _ -> 0 in
        match find_matching_record eee tm with If1.Som ii -> ii | _ -> 0)
    | If1.Som ii -> ii
  in
  let ff, (edghd, edgp, tty) = lll in
  let (bb, pp, t1), in_gr =
    If1.add_node_2
      (`Simple (If1.RBUILD, Array.make 2 ff, Array.make 1 "", [ If1.No_pragma ]))
      in_gr
  in
  let in_gr = If1.add_edge edghd edgp bb t1 tty in_gr in
  ((bb, pp, aout), in_gr)

and extract_vec_components (vn, vp, vt) dim in_gr =
  (* Extract `dim` scalar components from a vector via SWIZZLE nodes.
     Returns a list of (node, port, type) triples, one per component. *)
  let scalar_ty =
    let row_if1_ty = If1.lookup_ty vt in_gr in
    If1.find_ty in_gr (If1.get_element_type row_if1_ty)
  in
  List.fold_right
    (fun idx (acc, g) ->
      let (ln, lp, lt), g =
        If1.add_node_2 (`Literal (If1.INTEGRAL, string_of_int idx, [| "" |])) g
      in
      let (an, ap, at), g =
        If1.add_node_2 (`Simple (If1.ABUILD, [| "" |], [| "" |], [])) g
      in
      let g = If1.add_edge ln lp an 0 lt g in
      let (sn, sp, _), g =
        If1.add_node_2 (`Simple (If1.SWIZZLE, [| ""; "" |], [| "" |], [])) g
      in
      let g = If1.add_edge vn vp sn 0 vt g in
      let g = If1.add_edge an ap sn 1 at g in
      ((sn, sp, scalar_ty) :: acc, g))
    (List.init dim (fun i -> i))
    ([], in_gr)

and crack_swizzle_mask mask =
  let char_to_int = function
    | 'x' | 'r' | 's' | '0' -> 0
    | 'y' | 'g' | 't' | '1' -> 1
    | 'z' | 'b' | 'p' | '2' -> 2
    | 'w' | 'a' | 'q' | '3' -> 3
    | c -> failwith ("Invalid swizzle component: " ^ String.make 1 c)
  in
  List.init (String.length mask) (fun i -> char_to_int mask.[i])

and deduplicate_types typemap =
  (* 1. Helper to rewrite a type's internal labels based on a translation map *)
  let rewrite_labels subst_map ty =
    let find id = If1.TM.find_opt id subst_map |> Option.value ~default:id in
    match ty with
    | If1.Array_ty l -> If1.Array_ty (find l)
    | If1.Function_ty (l1, l2, s) -> If1.Function_ty (find l1, find l2, s)
    | If1.Record (l1, l2, s) -> If1.Record (find l1, find l2, s)
    | If1.Tuple_ty (l1, l2) -> If1.Tuple_ty (find l1, find l2)
    | If1.Union (l1, l2, s) -> If1.Union (find l1, find l2, s)
    | If1.Field labels -> If1.Field (List.map find labels)
    | If1.Tag labels -> If1.Tag (List.map find labels)
    | other -> other
  in

  (* 2. The Core Fold: Build a "Canonical Map" and a "Substitution Map" *)
  (* acc = (NewTypeMap, SubstitutionMap, StructToIdMap) *)
  let final_map, subst_map, _ =
    If1.TM.fold
      (fun id ty (new_map, subst, structs) ->
        let normalized_ty = rewrite_labels subst ty in
        match StructMap.find_opt normalized_ty structs with
        | Some existing_id ->
            (* Duplicate found! Map this ID to the one we already kept *)
            (new_map, If1.TM.add id existing_id subst, structs)
        | None ->
            (* First time seeing this structure; keep it *)
            ( If1.TM.add id normalized_ty new_map,
              If1.TM.add id id subst,
              StructMap.add normalized_ty id structs ))
      typemap
      (If1.TM.empty, If1.TM.empty, StructMap.empty)
  in
  (final_map, subst_map)

and check_rec_ty in_gr tty_lis tm outlis =
  match tty_lis with
  | (hdf, hd) :: tl ->
      let hdty =
        If1.TM.fold
          (fun k v z ->
            match z with
            | If1.Emp -> (
                let bar xx lt = if xx = hdf && lt = hd then If1.Som k else z in
                match v with
                | If1.Record (lt, _, xx) -> bar xx lt
                | If1.Union (lt, _, xx) -> bar xx lt
                | _ -> z)
            | _ -> z)
          tm If1.Emp
      in
      let _ =
        let hdmsg =
          Printf.sprintf "Unknown field in If1.record %s %d\n" hdf hd
        in
        match hdty with
        | If1.Som anum -> anum
        | If1.Emp ->
            print_endline (If1.str_type_trace ());
            let stack = Printexc.get_callstack 50 in
            (* Capture top 5 frames *)
            (*If1.dump_typemap tm;*)
            print_endline (Printexc.raw_backtrace_to_string stack);
            If1.If1_View.export_debug_html "CRASHED.html" in_gr;
            failwith hdmsg
      in
      hdty :: check_rec_ty in_gr tl tm outlis
  | [] -> outlis

and find_matching_record eee tm =
  If1.TM.fold
    (fun k v z ->
      match z with
      | If1.Emp -> (
          match v with
          | If1.Record (0, nxt, "") -> if nxt = eee then If1.Som k else z
          | _ -> z)
      | _ -> z)
    tm If1.Emp

and record_builder in_gr field_defs io_type =
  (* 1. Accumulate fields and update Graph state *)
  to_if1_msg 3 "record_builder: lowering %d field(s)" (List.length field_defs);
  let fields, in_gr =
    List.fold_left
      (fun (acc, g) (Ast.Field_def (Ast.Field_name fn, ex1)) ->
        to_if1_msg 3 "record_builder: lowering field %s" fn;
        let exp_l, g' = do_simple_exp g ex1 in
        ((fn, exp_l) :: acc, g'))
      ([], in_gr) field_defs
  in

  (* 2. Type Resolution & Validation *)
  let tm = If1.get_typemap_tm in_gr in
  let field_types = get_tys fields [] in
  let resolved_types = check_rec_ty in_gr field_types tm [] in

  (* Determine the output type index (aout) *)
  let aout =
    match io_type with
    | If1.Som ii -> ii
    | If1.Emp -> begin
        match resolved_types with
        | If1.Som head_type :: _ -> (
            match find_matching_record head_type tm with
            | If1.Som ii -> ii
            | If1.Emp ->
                failwith
                  "Record_builder: No matching record type found in Typemap")
        | _ -> failwith "Record_builder: Could not resolve field types"
      end
  in
  to_if1_msg 3 "record_builder: resolved output type %s" (If1.p_f_t in_gr aout);

  (* 3. Node Generation *)
  let num_fields = List.length field_defs in
  let node_config =
    `Simple
      ( If1.RBUILD,
        Array.make (num_fields + 1) "",
        (* Input ports: fields + optional base *)
        Array.make 1 "",
        (* Output ports *)
        [ If1.No_pragma ] )
  in

  let (node_id, port_id, _), in_gr = If1.add_node_2 node_config in_gr in
  to_if1_msg 3 "record_builder: RBUILD node %d, wiring fields: %s" node_id
    (String.concat "; "
       (List.map
          (fun (n, (_, _, z)) -> Printf.sprintf "%s:%s" n (If1.p_f_t in_gr z))
          fields));

  (* 4. Edge Wiring *)
  let in_gr = add_edges_for_fields (List.rev fields) node_id port_id in_gr in

  ((node_id, port_id, aout), in_gr)

and add_edges_in_list exp_list tail_node portnum in_gr =
  (* Add edges from tail_node, starting at portnum and
      ending IF1 node tuple *)
  match exp_list with
  | (head_node, head_port, tt) :: tl ->
      add_edges_in_list tl tail_node (portnum + 1)
        (If1.add_edge head_node head_port tail_node portnum tt in_gr)
  | [] -> in_gr

and do_iterator in_gr = function Ast.Repeat dp -> do_decldef_part in_gr dp

and do_termination in_gr = function
  | Ast.While e -> do_exp in_gr e
  | Until e ->
      let (en, ep, et), in_gr = do_exp in_gr e in
      let (nn, np, _), in_gr =
        If1.add_node_2
          (`Simple (If1.NOT, Array.make 1 "", Array.make 1 "", []))
          in_gr
      in
      let in_gr = If1.add_edge en ep nn 0 et in_gr in
      ((nn, np, If1.lookup_tyid If1.BOOLEAN), in_gr)

and do_constant in_gr xx =
  (* Return an IF1 node for
      constants *)
  let out_port_1 =
    let out_array = Array.make 1 "" in
    out_array
  in
  match xx with
  | Ast.False ->
      If1.add_node_2 (`Literal (If1.BOOLEAN, "False", out_port_1)) in_gr
  | Ast.Nil -> If1.add_node_2 (`Literal (If1.NULL, "Null", out_port_1)) in_gr
  | Ast.True ->
      If1.add_node_2 (`Literal (If1.BOOLEAN, "True", out_port_1)) in_gr
  | Ast.Int i ->
      If1.add_node_2
        (`Literal (If1.INTEGRAL, string_of_int i, out_port_1))
        in_gr
  | Ast.Float f ->
      If1.add_node_2 (`Literal (If1.REAL, string_of_float f, out_port_1)) in_gr
  | Ast.Char st ->
      If1.add_node_2 (`Literal (If1.CHARACTER, st, out_port_1)) in_gr
  | Ast.String st ->
      let (arr_char_ty, _, _), in_gr =
        If1.add_type_to_typemap_dedup
          (If1.Array_ty (If1.lookup_tyid If1.CHARACTER))
          in_gr
      in
      let (node_id, port_id, _), in_gr =
        If1.add_node_2 (`Literal (If1.CHARACTER, st, out_port_1)) in_gr
      in
      ((node_id, port_id, arr_char_ty), in_gr)
  | Ast.Error ast_typ ->
      let (_, _, err_ty_id), in_gr = If1.add_sisal_type in_gr ast_typ in
      let (_, _, _), in_gr =
        If1.add_type_to_typemap_dedup (Typed_error err_ty_id) in_gr
      in
      let node_config =
        `Simple
          ( If1.ERROR_NODE,
            Array.make 1 "",
            (* Input ports: fields + optional base *)
            Array.make 1 "",
            (* Output ports *)
            [ If1.No_pragma ] )
      in
      let (node_id, port_id, _), in_gr = If1.add_node_2 node_config in_gr in
      ((node_id, port_id, err_ty_id), in_gr)
  | Ast.Short s ->
      If1.add_node_2 (`Literal (If1.SHORT, string_of_int s, out_port_1)) in_gr
  | Ast.Ushort s ->
      If1.add_node_2 (`Literal (If1.USHORT, string_of_int s, out_port_1)) in_gr
  | Ast.Ubyte s ->
      If1.add_node_2 (`Literal (If1.UBYTE, string_of_int s, out_port_1)) in_gr
  | Ast.Byte s ->
      If1.add_node_2 (`Literal (If1.BYTE, string_of_int s, out_port_1)) in_gr
  | Ast.Uchar s ->
      If1.add_node_2 (`Literal (If1.UCHAR, string_of_int s, out_port_1)) in_gr
  | Ast.Uint s ->
      If1.add_node_2 (`Literal (If1.UINT, string_of_int s, out_port_1)) in_gr
  | Ast.Half f ->
      If1.add_node_2 (`Literal (If1.HALF, string_of_float f, out_port_1)) in_gr
  | Ast.Long s ->
      If1.add_node_2 (`Literal (If1.LONG, Int64.to_string s, out_port_1)) in_gr
  | Ast.Ulong s ->
      If1.add_node_2 (`Literal (If1.ULONG, Int64.to_string s, out_port_1)) in_gr
  | Ast.Double f ->
      If1.add_node_2
        (`Literal (If1.DOUBLE, string_of_float f, out_port_1))
        in_gr

and do_val_internal in_gr v =
  let ((nn, np, nty), in_gr), av =
    match v with
    | `Std10 v -> (If1.get_symbol_id v in_gr, v)
    | `OldMob v -> (If1.get_symbol_id_old v in_gr, v)
  in
  let nn, np, nty =
    match If1.get_node nn in_gr with
    (* TUPLE_VAL MULTIARITY: created by a #(…) expression and bound as a
       whole tuple to a variable.  Do NOT dereference — keep the MULTIARITY
       reference so that fold_away_multiarity_nodes can expand all ports when
       the tuple is used as a multi-value return, or follow a specific port
       when the same tuple is referenced multiple times (destructuring). *)
    | If1.Simple (_, If1.MULTIARITY, _, _, prags)
      when List.exists (function If1.Name "TUPLE_VAL" -> true | _ -> false) prags ->
        (nn, np, nty)
    (* Regular MULTIARITY: produced by a multi-return function call or
       other non-tuple multi-value context.  Dereference one level to the
       actual source at the specific symtab port — original behaviour. *)
    | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
        let nn, np, nty = If1.node_incoming_at_port nn np in_gr in
        (nn, np, nty)
    | _ -> (nn, np, nty)
  in
  ((nn, np, nty), in_gr)

and do_val in_gr = function
  (* Look up the node defining a variable *)
  | Ast.Value_name vl ->
      (* Flatten ["Math"; "PI"] into "Math.PI" for the symbol table *)
      let v = String.concat "." vl in
      do_val_internal in_gr (`Std10 v)

and do_exp in_gr = function
  (* Add an expression using add_exp *)
  | Ast.Exp e -> add_exp in_gr e 0 []
  | Empty -> ((0, 0, 0), in_gr)

and extr_types in_gr = function
  (* Look up type of If1.MULTIARITY *)
  | (xx, yy, zz), res ->
      let res, in_gr =
        let nm = in_gr.If1.nmap in
        let myn = If1.NM.find_opt xx nm in
        match myn with
        | Some (If1.Simple (_, If1.MULTIARITY, _, _, _)) ->
            let port_type_map =
              If1.all_types_ending_at_no_err_ty xx in_gr res
            in
            let k =
              If1.IntMap.filter
                (fun _ tid -> not (If1.is_error_port tid in_gr))
                port_type_map
            in
            (k, in_gr)
        | Some _ ->
            let res = If1.IntMap.add yy zz res in
            (res, in_gr)
        | _ -> failwith "failed to extract types in multiarity"
      in
      (res, in_gr)

and first_incoming_type_to_multiarity e in_gr =
  let pe = in_gr.If1.eset in
  let edges =
    If1.ES.filter
      (fun ((_, _), (y, _), ty_id) ->
        y = e && not (If1.is_error_port ty_id in_gr))
      pe
  in
  let _, _, t1 =
    assert (List.length (If1.ES.elements edges) <> 0);
    try List.hd (If1.ES.elements edges)
    with _ ->
      raise (If1.Sem_error "Error looking up first type in multiarity")
  in
  t1

and first_incoming_triple_to_multiarity e in_gr =
  let pe = in_gr.If1.eset in
  let edges = If1.ES.filter (fun ((_, _), (y, _), _) -> y = e) pe in
  let (x, xp), (_, _), aty =
    assert (List.length (If1.ES.elements edges) <> 0);
    try List.hd (If1.ES.elements edges)
    with _ ->
      raise
        (Format.printf "Error with incoming triple lookup for graph: %d" e;
         print_endline (If1.string_of_graph in_gr);
         Printexc.print_raw_backtrace stdout (Printexc.get_callstack 150);
         If1.Sem_error "Error looking up first triple in multiarity")
  in
  (x, xp, aty)

and add_exp in_gr ex _ ret_lis =
  (* Call do_simple_exp for each in list:ex and
      if there are multiple results, tie
      each result(s) to a If1.MULTIARITY node in
      sequentially numbered input ports
      in the same order as list:ex. Some simple exp
      may provide If1.MULTIARITY results-
      so handle those as well. If there is a single
      result, just return it without
      If1.MULTIARITY. *)
  match ex with
  | [] ->
      if List.length ret_lis <> 0 then
        let in_port_1 =
          let in_array = Array.make (List.length ret_lis) "" in
          in_array
        in
        let out_port_1 =
          let out_array = Array.make (List.length ret_lis) "" in
          out_array
        in
        let (oo, op, ot), in_gr =
          If1.add_node_2
            (`Simple
               (If1.MULTIARITY, in_port_1, out_port_1, [ If1.Name "FOR_DO_EXP" ]))
            in_gr
        in
        let nm = in_gr.If1.nmap in
        let is_tuple_val prags =
          List.exists (function If1.Name "TUPLE_VAL" -> true | _ -> false) prags
        in
        let expand_all_ports ahd atl oth_lis =
          let incoming = If1.all_edges_ending_at ahd in_gr in
          let sorted =
            List.sort
              (fun ((_, _), (_, yp1), _) ((_, _), (_, yp2), _) ->
                compare yp1 yp2)
              (If1.ES.elements incoming)
          in
          let nodes =
            List.map (fun ((x, xp), (_, _), ty) -> (x, xp, ty)) sorted
          in
          (nodes @ atl, oth_lis)
        in
        (* For TUPLE_VAL nodes pre-count occurrences in ret_lis.
           A tuple appearing once is a whole-tuple use → expand all ports.
           A tuple appearing multiple times means each reference is for a
           specific destructured element → follow only that port. *)
        let tuple_counts =
          List.fold_left
            (fun m (n, _, _) ->
              match If1.NM.find_opt n nm with
              | Some (If1.Simple (_, If1.MULTIARITY, _, _, prags))
                when is_tuple_val prags ->
                  let c = try If1.IntMap.find n m with Not_found -> 0 in
                  If1.IntMap.add n (c + 1) m
              | _ -> m)
            If1.IntMap.empty ret_lis
        in
        let rec fold_away_multiarity_nodes alis oth_lis =
          (* Move CAR from alis to oth_lis, but only
             when CAR is non-If1.MULTIARITY *)
          match alis with
          | (ahd, apo, aed_ty) :: atl ->
              let new_alis, new_oth_lis =
                match If1.NM.find_opt ahd nm with
                | Some (If1.Simple (_, If1.MULTIARITY, _, _, prags))
                  when is_tuple_val prags ->
                    (* TUPLE_VAL: use count to decide expand vs specific-port *)
                    let count =
                      try If1.IntMap.find ahd tuple_counts
                      with Not_found -> 1
                    in
                    if count <= 1 then
                      (* Whole-tuple use: expand all ports *)
                      expand_all_ports ahd atl oth_lis
                    else
                      (* Destructured: each ref carries its specific port *)
                      let src = If1.node_incoming_at_port ahd apo in_gr in
                      (src :: atl, oth_lis)
                | Some (If1.Simple (_, If1.MULTIARITY, _, _, _)) ->
                    (* Regular MULTIARITY (function return etc.): always expand *)
                    expand_all_ports ahd atl oth_lis
                | Some _ -> (atl, oth_lis @ [ (ahd, apo, aed_ty) ])
                | None -> failwith "Node not found, in To_if1:add_exp"
              in
              fold_away_multiarity_nodes new_alis new_oth_lis
          | [] -> (alis, oth_lis)
        in
        let _, ret_lis = fold_away_multiarity_nodes ret_lis [] in
        let rec add_all_edges_to_multiarity (mo, mp, mt) in_gr = function
          | [] -> ((mo, mp, mt), in_gr)
          | (hdn, hdp, hdt) :: tl ->
              add_all_edges_to_multiarity
                (mo, mp + 1, hdt)
                (If1.add_edge hdn hdp mo mp hdt in_gr)
                tl
        in
        let (_, _, ot), in_gr =
          add_all_edges_to_multiarity (oo, op, ot) in_gr ret_lis
        in
        ((oo, 0, ot), in_gr)
      else ((0, 0, 0), in_gr)
  | hde :: tl ->
      let (lasti, pp, tt1), in_gr_ = do_simple_exp in_gr hde in
      add_exp in_gr_ tl lasti (ret_lis @ [ (lasti, pp, tt1) ])

and do_field_name in_gr = function Ast.Field_name _ -> ((0, 0, 0), in_gr)

and do_field_exp in_gr = function
  | Ast.Field_exp (f, e) ->
      let _ = do_field in_gr f in
      do_simple_exp in_gr e

and do_field in_gr = function
  | Ast.Field f -> If1.add_each_in_list in_gr f 0 do_field_name

and do_field_def in_gr = function
  | Ast.Field_def (fn, ex) ->
      let _ = do_field_name in_gr fn in
      do_simple_exp in_gr ex

and do_in_exp ?(curr_level = 1) in_gr = function
  (* Inexp
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
  | Ast.In_exp (vn, e) ->
      let (aa, bb, cc), in_gr =
        match e with
        | Ast.Exp ei -> (
            match ei with
            | [ hd; tl ] ->
                (* Add each element in the exp to
                a range generator graph.\n*)
                bin_exp hd tl in_gr If1.RANGEGEN
            | [ hd ] ->
                let (e, pi, t1), in_gr = do_simple_exp in_gr hd in
                let (scatter, _, _), in_gr =
                  get_simple_unary 2 in_gr If1.ASCATTER
                in
                let t1 =
                  match If1.get_node e in_gr with
                  | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
                      let t1 = first_incoming_type_to_multiarity e in_gr in
                      t1
                  | _ -> t1
                in
                let outer_ty_num, inner_ty_num =
                  let rec walk_ty curr_ty curr_l =
                    let lookup_array_ty curr_ty in_gr =
                      match If1.lookup_ty curr_ty in_gr with
                      | If1.Array_ty ij -> (curr_ty, ij)
                      | If1.Stream ij -> (curr_ty, ij)
                      | _ ->
                          raise
                            (If1.Sem_error
                               ("Array type expected"
                              ^ " when constructing If1.ASCATTER"
                              ^ string_of_int curr_ty))
                    in
                    if curr_l = curr_level then lookup_array_ty curr_ty in_gr
                    else
                      let _, inner_ty_num = lookup_array_ty curr_ty in_gr in
                      walk_ty inner_ty_num (curr_l + 1)
                  in
                  walk_ty t1 1
                in
                let in_gr = If1.add_edge e pi scatter 0 outer_ty_num in_gr in
                ((scatter, 0, inner_ty_num), in_gr)
            | _ ->
                raise
                  (If1.Sem_error
                     ("Unsupported arity for in exp,"
                    ^ " must be 1 for array and 2 for"
                    ^ " comma separated bounds.\n")))
        | _ ->
            raise
              (If1.Sem_error
                 ("Unsupported arity for in exp,"
                ^ " must be 1 for array and 2 for"
                ^ " comma separated bounds.\n"))
      in
      let in_gr =
        let cs, ps = in_gr.If1.symtab in
        match vn with
        | Ast.Value_name vl ->
            let v = String.concat "." vl in

            {
              in_gr with
              If1.symtab =
                ( If1.SM.add v
                    {
                      If1.val_name = v;
                      If1.val_ty = cc;
                      If1.val_def = aa;
                      If1.def_port = bb;
                    }
                    cs,
                  ps );
            }
      in
      let in_gr =
        If1.output_to_boundary
          ~start_port:(If1.boundary_in_port_count in_gr)
          [ (aa, bb, cc) ]
          in_gr
      in
      ((aa, bb, cc), in_gr)
  | Ast.At_exp (ie, vns) ->
      (* The optional at clause is present in an in-exp.
        The value names following "at" denote index values of type
        integer corresponding to the current element value's
        position in the array. It is an error if the
        number of value names in the index list is greater than the
        number of dimensions of the array expression.
        The range of the for expression is the cross product
        over the number of ranges specified by the number of
        names in the index list. *)
      let (aa, bb, cc), in_gr = do_in_exp ~curr_level in_gr ie in
      let in_gr =
        let cs, ps = in_gr.If1.symtab in
        match vns with
        | Value_names v ->
            {
              in_gr with
              If1.symtab =
                (let vv = List.nth v (curr_level - 1) in
                 ( If1.SM.add vv
                     {
                       If1.val_name = vv;
                       If1.val_ty = If1.lookup_tyid If1.INTEGRAL;
                       If1.val_def = aa;
                       If1.def_port = bb + 1;
                     }
                     cs,
                   ps ));
            }
      in
      let in_gr =
        If1.output_to_boundary
          ~start_port:(If1.boundary_in_port_count in_gr)
          [ (aa, bb + 1, If1.lookup_tyid If1.LONG) ]
          in_gr
      in
      ((aa, bb, cc), in_gr)
  | Ast.Dot (ie1, ie2) ->
      let _, in_gr = do_in_exp in_gr ie1 in
      let (x, y, z), in_gr = do_in_exp in_gr ie2 in
      ((x, y, z), in_gr)
  | Ast.Cross (_, _) -> raise (If1.Sem_error "Need to be in a forall context")

and get_lower_lim = function
  | Ast.Cross (_, _) ->
      raise (If1.Sem_error "Cannot be used in a forall context")
  | Ast.Dot (ie1, _) -> get_lower_lim ie1
  | Ast.At_exp (_, _) ->
      raise (If1.Sem_error "Cannot be used in a forall context")
  | Ast.In_exp (_, Ast.Exp e) -> (
      try List.hd e
      with _ ->
        raise (If1.Sem_error "Error Ast.while obtaining lower_lim for forall"))
  | _ -> raise (If1.Sem_error "Error Ast.while obtaining lower_lim for forall")

and build_alim in_gr =
  (* Helper function to build an ALim node *)
  let in_port_1 =
    let in_array = Array.make 2 "" in
    in_array
  in
  let out_port_1 =
    let out_array = Array.make 2 "" in
    out_array
  in
  If1.add_node_2
    (`Simple (If1.ALIML, in_port_1, out_port_1, [ If1.Name "ALimL" ]))
    in_gr

and build_multiarity ?(nam = "") siz in_gr =
  (* Helper function building a If1.MULTIARITY node *)
  let in_port_1 =
    let in_array = Array.make siz "" in
    in_array
  in
  let out_port_1 =
    let out_array = Array.make siz "" in
    out_array
  in
  If1.add_node_2
    (`Simple
       ( If1.MULTIARITY,
         in_port_1,
         out_port_1,
         [ If1.Name ("multiARITY_" ^ nam) ] ))
    in_gr

and get_ports_unified of_gr basis_gr parent_gr =
  (* Take basis_gr:boundary and add them to of_gr:boundary
        with the same port numbers. Confirm that parent_gr
        contains the symbol, i.e., restrict to outer
        scope variables.*)
  let bin = If1.get_boundary_node basis_gr in
  match bin with
  | If1.Boundary (in_port_lis, _, _, _) ->
      List.fold_right
        (fun (_, xp, xn) f_gr ->
          if If1.is_outer_var xn parent_gr = true then
            let cs, ps = f_gr.If1.symtab in
            if If1.SM.mem xn ps = true then
              let {
                If1.val_ty = t;
                If1.val_name = _;
                If1.val_def = _;
                If1.def_port = _;
              } =
                If1.SM.find xn ps
              in
              let f_gr =
                {
                  f_gr with
                  If1.symtab =
                    ( If1.SM.add xn
                        {
                          If1.val_ty = t;
                          If1.val_name = xn;
                          If1.val_def = 0;
                          If1.def_port = xp;
                        }
                        cs,
                      ps );
                }
              in
              If1.add_to_boundary_inputs ~namen:xn 0 xp f_gr
            else raise (If1.Sem_error ("Cannot find name in outer scope:" ^ xn))
          else f_gr)
        in_port_lis of_gr
  | _ -> of_gr

and tie_outer_scope_to_inner from_gr to_gr to_node =
  (* Tie outer scope variables to forall boundary
      input ports. *)
  let bin = If1.get_boundary_node from_gr in
  match bin with
  | If1.Boundary (in_port_lis, _, _, _) ->
      List.fold_right
        (fun (_, yp, xn) o_gr ->
          let (xx, xy, xt), o_gr = If1.get_symbol_id xn o_gr in
          If1.add_edge xx xy to_node yp xt o_gr)
        in_port_lis to_gr
  | _ -> to_gr

and do_for_all inexp bodyexp retexp in_gr =
  (* Use Array input's dimensions to
      set Array output's dimensions*)
  let fall = Ast.For_all (inexp, bodyexp, retexp) in
  let rec get_cross_exp_lis inexp retl =
    (* Create a list of index expressions.
        Ast.Cross would be for nested loops and so would At.*)
    match inexp with
    | Ast.Cross (ie1, ie2) -> get_cross_exp_lis ie1 ((1, ie2) :: retl)
    | Ast.At_exp (_, Value_names vns) ->
        let _, oul =
          List.fold_right
            (fun _ (lev, re) -> (lev - 1, (lev, inexp) :: re))
            vns
            (List.length vns, [])
        in
        oul
    | aie ->
        (* single nest case *)
        (1, aie) :: retl
  in

  let generator_array_lowlim in_gr =
    (* Check if we have an If1.ASCATTER or
        Counted loop in the generator *)
    try
      `ArrLim
        (If1.NM.fold
           (fun _ vv ooo ->
             match vv with
             | If1.Simple (lab, If1.ASCATTER, _, _, _) ->
                 raise (If1.Val_is_found lab)
             | _ -> ooo)
           in_gr.If1.nmap 0)
    with If1.Val_is_found xyz -> `AScatt xyz
  in

  let add_asetl_for_array_res outer_gen_gr gen_exp_outer in_gr fx aa tt cc mul_n
      =
    let aar = generator_array_lowlim outer_gen_gr in
    match aar with
    | `ArrLim xy ->
        let ainx = get_lower_lim gen_exp_outer in
        let (ai, ay, _), in_gr = do_simple_exp in_gr ainx in
        let (aa1, _, _), in_gr = unary_internal 1 fx aa tt in_gr If1.ASETL in
        let in_gr =
          If1.add_edge ai ay aa1 1 (If1.lookup_tyid If1.INTEGRAL) in_gr
        in
        let in_gr =
          if mul_n = 0 then
            If1.add_to_boundary_outputs ~start_port:cc aa1 0 tt in_gr
          else If1.add_edge2 aa1 0 mul_n cc tt in_gr
        in
        (xy, in_gr)
    | `AScatt xy ->
        let x, xx, xxx = If1.node_incoming_at_port xy 0 outer_gen_gr in
        let (ix, _, _), in_gr = build_alim in_gr in
        let in_gr = If1.add_edge x xx ix 0 xxx in_gr in
        let (aa1, _, _), in_gr = unary_internal 2 fx aa tt in_gr If1.ASETL in
        let in_gr = If1.add_edge ix 0 aa1 1 5 in_gr in
        let in_gr =
          if mul_n = 0 then If1.add_to_boundary_outputs aa1 cc tt in_gr
          else If1.add_edge2 aa1 cc mul_n cc tt in_gr
        in
        (aa1, in_gr)
  in

  let build_gen_graph curr_lev in_gr gen_exp =
    to_if1_msg 3 "For_all: lowering GENERATOR (level %d)" curr_lev;
    let gen_gr = get_ports_unified (If1.get_a_new_graph in_gr) in_gr in_gr in
    let xyz, gen_gr = do_in_exp ~curr_level:curr_lev gen_gr gen_exp in
    let gen_gr =
      { gen_gr with If1.typemap = If1.get_merged_typeblob_gr in_gr gen_gr }
    in
    (xyz, gen_gr)
  in

  let rec build_forloop inexp bodyexp retexp in_gr =
    match inexp with
    | [] -> raise (If1.Sem_error "Internal Compiler Error")
    | (curr_lev, gen_exp_inner) :: [] ->
        (* In_Gr Must Be Based On An Outer Gen_Gr. *)
        let _, gen_gr = build_gen_graph curr_lev in_gr gen_exp_inner in

        (* Put The Decldefs (Loop Code) In The Body. *)
        to_if1_msg 3 "For_all: lowering BODY";
        let _, body_gr =
          (* Create Body Graph Based On In_Gr. *)
          let body_gr =
            If1.inherit_parent_syms gen_gr (If1.get_a_new_graph gen_gr)
          in

          let body_gr = get_ports_unified body_gr gen_gr gen_gr in

          do_decldef_part body_gr bodyexp
        in
        (* Insert Expressions Inside Return Clauses To Body Graph. *)
        to_if1_msg 3 "For_all: lowering RETURNS";
        let body_gr, return_action_list, ret_tuple_list, mask_ty_list =
          do_returns_clause_list body_gr retexp [] [] []
        in

        (* Connect Results To Body's If1.Boundary *)
        let body_gr = If1.output_to_boundary ret_tuple_list body_gr in
        (* Connect Results To Body's If1.Boundary *)
        let body_gr = If1.output_to_boundary_with_none mask_ty_list body_gr in

        let (rn, _, _), forall_gr, return_action_list =
          add_ret body_gr return_action_list mask_ty_list
            (String.concat "\n" (List.map Ast.str_return_clause retexp))
        in

        let (gn, _, _), forall_gr =
          If1.add_node_2
            (`Compound (gen_gr, If1.INTERNAL, 0, [ If1.Name "GENERATOR" ], []))
            forall_gr
        in

        let (bx, by, bz), forall_gr =
          If1.add_node_2
            (`Compound (body_gr, If1.INTERNAL, 0, [ If1.Name "BODY" ], []))
            forall_gr
        in

        let forall_gr = get_ports_unified forall_gr body_gr gen_gr in

        ( (bx, by, bz),
          return_action_list,
          mask_ty_list,
          forall_gr,
          [ gn; bx; rn ] )
    | (curr_lev, gen_exp) :: gen_exp_tl ->
        let ( (inner_gen_n, inner_gen_p, inner_gen_ty),
              inner_ret,
              mask_ty_list,
              forall_gr,
              inner_ids ) =
          (* Create A Generator For Outer Loop. *)
          let (_, _, _), gen_gr = build_gen_graph curr_lev in_gr gen_exp in

          (* Add outer loop generator to a new forall_gr. *)
          let (gn, _, _), forall_gr =
            let forall_gr =
              get_ports_unified (If1.get_a_new_graph gen_gr) gen_gr gen_gr
            in
            If1.add_node_2
              (`Compound (gen_gr, If1.INTERNAL, 0, [ If1.Name "GENERATOR" ], []))
              forall_gr
          in

          let _, inner_ret, mask_ty_list, body_nest_gr, inner_ids =
            (* As The Body Would Need Outer And Inner Generators,
              Send Gen_Gr To The Recursive Call To Obtain
              The Inner Loop, Which Is Body_Nest_Gr. *)
            build_forloop gen_exp_tl bodyexp retexp
              (get_ports_unified (If1.get_a_new_graph gen_gr) gen_gr gen_gr)
          in

          (* Add Returns Graph To Forall_Gr. *)
          let (rn, _, _), forall_gr, return_action_list =
            let _, mask_ty_list = organize_ret_info inner_ret mask_ty_list in
            add_return_gr forall_gr gen_gr inner_ret mask_ty_list ""
          in

          (* Add Body_Nest_Gr In Place Of A "Body" Subgraph. *)
          let (fx, fy, fz), forall_gr =
            If1.add_node_2
              (`Compound
                 ( body_nest_gr,
                   If1.INTERNAL,
                   0,
                   [ If1.Name "FORALL" ],
                   inner_ids ))
              forall_gr
          in

          let _, _, forall_gr =
            (* Get Generator'S Lower Size Setting
              And Add To Asetl. After That Abstract This
              And  Call From Outside As Well. *)
            List.fold_right
              (fun (wh, tt, aa) (cc, outl, in_gr) ->
                match wh with
                | `Array_of ->
                    let ouln, in_gr =
                      add_asetl_for_array_res gen_gr gen_exp in_gr fx aa tt cc 0
                    in
                    (cc + 1, (wh, tt, ouln, cc) :: outl, in_gr)
                | _ ->
                    let in_gr = If1.add_to_boundary_outputs fx cc tt in_gr in
                    (cc + 1, (wh, tt, fx, cc) :: outl, in_gr))
              return_action_list (0, [], forall_gr)
          in

          let forall_gr =
            let forall_gr = get_ports_unified forall_gr body_nest_gr gen_gr in
            tie_outer_scope_to_inner forall_gr forall_gr fx
          in

          ( (fx, fy, fz),
            return_action_list,
            mask_ty_list,
            forall_gr,
            [ gn; fx; rn ] )
        in
        ( (inner_gen_n, inner_gen_p, inner_gen_ty),
          inner_ret,
          mask_ty_list,
          forall_gr,
          inner_ids )
  in

  let acrossl = get_cross_exp_lis inexp [] in
  let _, return_action_list, _, forall_gr, subgr_ids =
    build_forloop acrossl bodyexp retexp in_gr
  in
  let forall_gr = get_ports_unified forall_gr forall_gr forall_gr in
  let (fx, _, _), in_gr =
    If1.add_node_2
      (`Compound
         ( forall_gr,
           If1.INTERNAL,
           0,
           [ If1.Name "FORALL"; If1.Ast_type (Ast.str_simple_exp fall) ],
           subgr_ids ))
      in_gr
  in

  let (mul_n, mul_p, mul_t), in_gr =
    build_multiarity ~nam:"FOR_ALL" (List.length return_action_list) in_gr
  in

  let _, _, in_gr =
    List.fold_right
      (fun (wh, tt, aa) (cc, outl, iigr) ->
        match wh with
        | `Array_of ->
            let ouln, iigr =
              let _, gen_exp =
                try List.hd acrossl
                with _ -> raise (If1.Sem_error "Error lowering gen_exp")
              in
              add_asetl_for_array_res (get_gen_graph forall_gr) gen_exp iigr fx
                aa tt cc mul_n
            in
            (cc + 1, (wh, tt, ouln, cc) :: outl, iigr)
        | _ ->
            ( cc + 1,
              (wh, tt, fx, cc) :: outl,
              If1.add_edge2 fx aa mul_n cc tt iigr ))
      return_action_list (0, [], in_gr)
  in

  let in_gr = tie_outer_scope_to_inner forall_gr in_gr fx in
  ((mul_n, mul_p, mul_t), return_action_list, in_gr)

and do_decldef_part in_gr = function
  | Ast.Decldef_part f ->
      (* This version of do_decldef_part
       is similar to a Let ... in
       usage. The LHS names are exposed to the
       RHS in the following statements.*)
      let xyz, in_gr =
        let rec process_each_in_list f xyz in_gr =
          match f with
          | decldef_hd :: decldefs_tl ->
              let xyz, in_gr = do_decldef in_gr decldef_hd in
              process_each_in_list decldefs_tl xyz in_gr
          | [] -> (xyz, in_gr)
        in
        process_each_in_list f (0, 0, 0) in_gr
      in
      (xyz, in_gr)

and do_decldef_part_in_let_stmt kind in_gr = function
  | Ast.Decldef_part f ->
      let in_gr =
        match kind with
        | `Some _ ->
            let rec process_each_in_list f in_gr =
              match f with
              | decldef_hd :: decldefs_tl ->
                  let in_gr = do_decldef_let_rec_symbols in_gr decldef_hd in
                  process_each_in_list decldefs_tl in_gr
              | [] -> in_gr
            in
            process_each_in_list f in_gr
        | `None -> in_gr
      in
      let xyz, _, _, in_gr =
        let rec process_each_in_list f xyz expl_rev decl_rev in_gr =
          match f with
          | decldef_hd :: decldefs_tl ->
              let xyz, expl_rev, decl_rev, in_gr =
                match kind with
                | `None -> do_decldef2 in_gr decldef_hd expl_rev decl_rev
                | `Some _ ->
                    do_decldef_let_rec in_gr decldef_hd expl_rev decl_rev
              in
              process_each_in_list decldefs_tl xyz expl_rev decl_rev in_gr
          | [] -> (xyz, expl_rev, decl_rev, in_gr)
        in
        process_each_in_list f (0, 0, 0) [] [] in_gr
      in
      (xyz, in_gr)

and do_params_decl po in_gr z =
  match z with
  | Ast.Decl_with_type (x, y) ->
      let type_num, in_gr =
        let (id_t, _, _), in_gr = If1.add_sisal_type in_gr y in
        (id_t, in_gr)
      in
      let u, v = in_gr.If1.symtab in
      let rec add_all_to_sm umap xli p q in_gr =
        match xli with
        | Ast.Decl_name hdx :: tlx ->
            let port = p + po in
            let sm_v =
              {
                If1.val_name = hdx;
                If1.val_ty = type_num;
                If1.val_def = 0;
                If1.def_port = port;
              }
            in
            let in_gr = If1.add_to_boundary_inputs ~namen:hdx 0 port in_gr in
            add_all_to_sm (If1.SM.add hdx sm_v umap) tlx (p + 1) (hdx :: q)
              in_gr
        | Decl_func _ :: _ ->
            raise (If1.Sem_error "Ast.Function_header by assign TODO")
        | [] -> (p, q, umap, in_gr)
      in
      let p, q, u, in_gr = add_all_to_sm u x 0 [] in_gr in
      ((p + po, q, type_num), { in_gr with If1.symtab = (u, v) })
  | Decl_no_type _ -> raise (If1.Sem_error "Declaration must provide a type")
  | Decl_tuple_no_type _ | Decl_tuple_with_type _ ->
      raise
        (If1.Sem_error "Tuple pattern in function parameters not yet supported")

and extract_types_from_decl_list dl =
  List.fold_left
    (fun dlz dlx ->
      dlz
      @
      match dlx with
      | Ast.Decl_with_type (x, aty) -> List.map (fun _ -> aty) x
      | Decl_no_type _ ->
          raise
            (If1.Sem_error
               "Declaration without a type spec is not allowed in this context")
      | Decl_tuple_no_type _ | Decl_tuple_with_type _ ->
          raise
            (If1.Sem_error "Tuple decl in type extraction not yet supported"))
    [] dl

and do_decldef in_gr delc =
  let rec check_decl_type atyp expty in_gr =
    match atyp with
    | Some atype ->
        let (_, _, typenum), in_gr = If1.add_sisal_type in_gr atype in
        if typenum <> expty then
          (* Allow numeric widening/narrowing coercions *)
          let is_numeric_compat =
            match (numeric_rank expty in_gr, numeric_rank typenum in_gr) with
            | Some _, Some _ -> true
            | _ -> false
          in
          if is_numeric_compat then in_gr
          else
            raise
              (print_string " Inferred type: ";
               print_int expty;
               print_string " (";
               print_string (If1.p_f_t in_gr expty);
               print_string ") Expected type: ";
               print_int typenum;
               print_string " (";
               print_string (If1.p_f_t in_gr typenum);
               print_string ")";
               print_endline "";
               print_endline (Ast.str_sisal_type atype);
               If1.Sem_error " Incorrect expression type bound to declaration")
        else in_gr
    | None -> in_gr
  (* let check_decl_type *)
  and do_each_decl lhs_decl_names rhs_exps expl in_gr =
    match lhs_decl_names with
    | Ast.Decl_with_type (decls, atype) :: decllist_tail ->
        let expl, rhs_exps, in_gr =
          bind_exp_to_decl expl rhs_exps decls (Some atype) in_gr
        in
        do_each_decl decllist_tail rhs_exps expl in_gr
    | Decl_no_type decls :: decllist_tail ->
        let expl, rhs_exps, in_gr =
          bind_exp_to_decl expl rhs_exps decls None in_gr
        in
        do_each_decl decllist_tail rhs_exps expl in_gr
    | Decl_tuple_no_type decl_names :: decllist_tail ->
        let expl, rhs_exps, in_gr =
          bind_exp_to_decl expl rhs_exps decl_names None in_gr
        in
        do_each_decl decllist_tail rhs_exps expl in_gr
    | Decl_tuple_with_type (decl_names, type_list) :: decllist_tail ->
        let expl, rhs_exps, in_gr =
          if List.length decl_names = List.length type_list then
            List.fold_left2
              (fun (expl, rhs, igr) dn typ ->
                bind_exp_to_decl expl rhs [dn] (Some typ) igr)
              (expl, rhs_exps, in_gr) decl_names type_list
          else
            bind_exp_to_decl expl rhs_exps decl_names None in_gr
        in
        do_each_decl decllist_tail rhs_exps expl in_gr
    | [] -> in_gr
  and pop_or_push_to_exp_stack expl rhs_exps in_gr =
    match expl with
    | head_expl :: tl_expl -> (head_expl, rhs_exps, tl_expl, in_gr)
    | [] ->
        if List.length rhs_exps = 0 then (
          Printexc.print_raw_backtrace stdout (Printexc.get_callstack 50);
          flush stdout);
        assert (List.length rhs_exps <> 0);
        let exphhd = List.hd rhs_exps in
        let (expnum, expport, expty), in_gr = do_simple_exp in_gr exphhd in
        let expty =
          match If1.get_node expnum in_gr with
          | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
              first_incoming_type_to_multiarity expnum in_gr
          | _ -> expty
        in
        let expl =
          match If1.get_node expnum in_gr with
          | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
              let port_type_map =
                If1.all_types_ending_at_no_err_ty expnum in_gr If1.IntMap.empty
              in
              let port_type_map =
                If1.IntMap.filter
                  (fun _ tid -> not (If1.is_error_port tid in_gr))
                  port_type_map
              in
              If1.IntMap.fold
                (fun ke va retl ->
                  (* Resolve through the MULTIARITY to the actual producer so that
                     if this name is later returned as a boundary output,
                     point_edges_to_boundary sees the real node — not the MULTIARITY —
                     and does not incorrectly unravel all ports. *)
                  let actual = If1.find_incoming_regular_node (expnum, ke, va) in_gr in
                  actual :: retl)
                port_type_map expl
          | _ -> (expnum, expport, expty) :: expl
        in
        let expl = List.rev expl in
        let expl_hd =
          match expl with hd_expl :: _ -> hd_expl | [] -> (0, 0, 0)
        in
        let expl_tl = match expl with _ :: tl_expl -> tl_expl | [] -> [] in
        let xom =
          match rhs_exps with
          | _ :: exp_tl -> (expl_hd, exp_tl, expl_tl, in_gr)
          | [] -> (expl_hd, [], expl_tl, in_gr)
        in
        xom
  and bind_exp_to_decl expl rhs_exps decls atyp in_gr =
    match decls with
    | current_name :: remaining_names ->
        (* ending let (expnum, expport, ...) *)
        let expl, rhs_exps, in_gr =
          match current_name with
          | Ast.Decl_name current_name ->
              let (expnum, expport, expty), rhs_exps, expl, in_gr =
                pop_or_push_to_exp_stack expl rhs_exps in_gr
              in
              let in_gr = check_decl_type atyp expty in_gr in
              let localsyms, globsyms = in_gr.If1.symtab in
              ( expl,
                rhs_exps,
                {
                  in_gr with
                  If1.symtab =
                    ( If1.SM.add current_name
                        {
                          If1.val_name = current_name;
                          If1.val_ty = expty;
                          If1.val_def = expnum;
                          If1.def_port = expport;
                        }
                        localsyms,
                      globsyms );
                } )
          | Decl_func current_name ->
              let (_, _, _), in_gr_ =
                do_function_header (If1.get_a_new_graph in_gr) current_name
              in
              let fn =
                match current_name with
                | Ast.Function_header (Ast.Function_name fn_path, _, _) ->
                    String.concat "." fn_path
                | Ast.Function_header_nodec (Ast.Function_name fn_path, _) ->
                    String.concat "." fn_path
              in
              let (_, _, expty), rhs_exps, expl, in_gr_ =
                pop_or_push_to_exp_stack expl rhs_exps in_gr_
              in
              let in_gr_ = check_decl_type atyp expty in_gr_ in
              let in_gr_ = If1.graph_clean_multiarity in_gr_ in
              let _, in_gr =
                If1.add_node_2
                  (`Compound (in_gr_, If1.INTERNAL, 0, [ If1.Name fn ], []))
                  in_gr
              in
              (expl, rhs_exps, in_gr)
        in
        bind_exp_to_decl expl rhs_exps remaining_names atyp in_gr
    | [] -> (expl, rhs_exps, in_gr)
  in
  match delc with
  | Ast.Decldef (lhs_decl_names, Ast.Exp rhs_exps) ->
      (* Ast.Decldef:
       First component in a Ast.Decldef is a list of
       lists of declids. Each list is either a
       Ast.Decl_with_type type-spec or Decl_no_type.

       Second component in a Ast.Decldef is
       an exp-list. There is no one-one
       correspondance between each decl
       and each exp. Only after an exp is
       lowered do we have one-one connectivity. *)
      (* Grammar produces declids_typed groups in reverse source order; reverse. *)
      let lhs_decl_names = List.rev lhs_decl_names in
      ((0, 0, 0), do_each_decl lhs_decl_names rhs_exps [] in_gr)
  | _ -> raise (If1.Sem_error "Internal compiler error")

and check_decl_type atyp expty in_gr =
  match atyp with
  | Some atype ->
      let (_, _, typenum), in_gr = If1.add_sisal_type in_gr atype in
      if typenum <> expty then
        let is_numeric_compat =
          match (numeric_rank expty in_gr, numeric_rank typenum in_gr) with
          | Some _, Some _ -> true
          | _ -> false
        in
        if is_numeric_compat then in_gr
        else
          raise
            (print_endline (If1.str_type_trace ());
             print_string " Inferred type: ";
             print_int expty;
             print_string " (";
             print_string (If1.p_f_t in_gr expty);
             print_string ") Expected type: ";
             print_int typenum;
             print_string " (";
             print_string (If1.p_f_t in_gr typenum);
             print_string ")";
             print_endline "";
             print_endline (Ast.str_sisal_type atype);
             If1.Sem_error " Incorrect expression type bound to declaration")
      else in_gr
  | None -> in_gr
(* let check_decl_type *)

and do_each_decl2 lhs_decldef_names rhs_decldef_exps expl expl_rev decl_rev
    in_gr =
  match lhs_decldef_names with
  | Ast.Decl_with_type (decl_names, atype) :: decllist_tail ->
      let expl, expl_rev, decl_rev, rhs_decldef_exps, in_gr =
        (* Take the first LHS item and get the rhs expression lowered.
         * There can be more than one name. So each group may
         * expect the expression to have as many results as
         * names in the group. In this decl, the expected type
         * of each name is also given in the source. *)
        do_exp_for_decl expl expl_rev decl_rev rhs_decldef_exps decl_names
          (Some atype) in_gr
      in
      (* Now go on to the next decl in the LHS. *)
      do_each_decl2 decllist_tail rhs_decldef_exps expl expl_rev decl_rev in_gr
  | Decl_no_type decl_names :: decllist_tail ->
      let expl, expl_rev, decl_rev, rhs_decldef_exps, in_gr =
        (* Same as above, but no types are attached to the LHS names *)
        do_exp_for_decl expl expl_rev decl_rev rhs_decldef_exps decl_names None
          in_gr
      in
      (* Now go on to the next decl in the LHS. *)
      do_each_decl2 decllist_tail rhs_decldef_exps expl expl_rev decl_rev in_gr
  | Decl_tuple_no_type decl_names :: decllist_tail ->
      let expl, expl_rev, decl_rev, rhs_decldef_exps, in_gr =
        do_exp_for_decl expl expl_rev decl_rev rhs_decldef_exps decl_names None in_gr
      in
      do_each_decl2 decllist_tail rhs_decldef_exps expl expl_rev decl_rev in_gr
  | Decl_tuple_with_type (decl_names, type_list) :: decllist_tail ->
      let expl, expl_rev, decl_rev, rhs_decldef_exps, in_gr =
        if List.length decl_names = List.length type_list then
          List.fold_left2
            (fun (expl, xrev, drev, rhs, igr) dn typ ->
              do_exp_for_decl expl xrev drev rhs [dn] (Some typ) igr)
            (expl, expl_rev, decl_rev, rhs_decldef_exps, in_gr)
            decl_names type_list
        else
          do_exp_for_decl expl expl_rev decl_rev rhs_decldef_exps decl_names None in_gr
      in
      do_each_decl2 decllist_tail rhs_decldef_exps expl expl_rev decl_rev in_gr
  | [] -> (expl_rev, decl_rev, in_gr)

and do_exp_for_decl exp_stack expl_rev decl_rev rhs_exps lhs_names atyp in_gr =
  match lhs_names with
  | current_name :: remaining_names ->
      (* ending let (expnum, expport, ...) *)
      let exp_stack, expl_rev, decl_rev, rhs_exps, in_gr =
        match current_name with
        | Ast.Decl_name current_name ->
            (* current_name are each of the names that are on the LHS *)
            let (expnum, expport, expty), rhs_exps, exp_stack, in_gr, expl_rev =
              pop_or_push_to_exp_stack2 exp_stack expl_rev rhs_exps in_gr
            in
            (* if atyp is set, it needs to be the same as the lowered
             * expression's type *)
            let in_gr = check_decl_type atyp expty in_gr in
            let localsyms, globsyms = in_gr.If1.symtab in
            let localsyms =
              If1.SM.add current_name
                {
                  If1.val_name = current_name;
                  If1.val_ty = expty;
                  If1.val_def = expnum;
                  If1.def_port = expport;
                }
                localsyms
            in
            let in_gr = { in_gr with If1.symtab = (localsyms, globsyms) } in
            (exp_stack, expl_rev, current_name :: decl_rev, rhs_exps, in_gr)
        | Decl_func current_name ->
            let fn, _ =
              match current_name with
              | Ast.Function_header (Ast.Function_name fn_path, decls, _) ->
                  (String.concat "." fn_path, decls)
              | Ast.Function_header_nodec (Ast.Function_name fn_path, _) ->
                  (String.concat "." fn_path, [])
            in
            let (_, funport, funty), in_gr_ =
              do_function_header
                (If1.inherit_parent_syms in_gr (If1.get_a_new_graph in_gr))
                current_name
            in
            let (_, _, expty), rhs_exps, exp_stack, in_gr_, expl_rev =
              pop_or_push_to_exp_stack2 exp_stack expl_rev rhs_exps in_gr_
            in
            let in_gr_ = check_decl_type atyp expty in_gr_ in
            let in_gr_ = If1.graph_clean_multiarity in_gr_ in
            let (expnum, _, _), in_gr =
              If1.add_node_2
                (`Compound (in_gr_, If1.INTERNAL, 0, [ If1.Name fn ], []))
                in_gr
            in
            let localsyms, globsyms = in_gr.If1.symtab in
            let localsyms =
              If1.SM.add fn
                {
                  If1.val_name = fn;
                  If1.val_ty = funty;
                  If1.val_def = expnum;
                  If1.def_port = funport;
                }
                localsyms
            in
            let in_gr = { in_gr with If1.symtab = (localsyms, globsyms) } in
            ( exp_stack,
              (expnum, funport, funty) :: expl_rev,
              fn :: decl_rev,
              rhs_exps,
              in_gr )
      in
      do_exp_for_decl exp_stack expl_rev decl_rev rhs_exps remaining_names atyp
        in_gr
  | [] -> (exp_stack, expl_rev, decl_rev, rhs_exps, in_gr)

and pop_or_push_to_exp_stack2 exp_stack expl_in_rev rhs_exps in_gr =
  (* Check if there is an item in the first list;
   * else we need to look in the rhs_exps.
   * Put the head of the list in a return
   * list in reverse. *)
  match exp_stack with
  | hd_exp_stack :: tl_exp_stack ->
      (hd_exp_stack, rhs_exps, tl_exp_stack, in_gr, hd_exp_stack :: expl_in_rev)
  | [] ->
      assert (List.length rhs_exps > 0);
      let exphhd = List.hd rhs_exps in
      let (expnum, expport, expty), in_gr = do_simple_exp in_gr exphhd in
      let expty =
        match If1.get_node expnum in_gr with
        | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
            first_incoming_type_to_multiarity expnum in_gr
        | _ -> expty
      in
      let exp_stack =
        match If1.get_node expnum in_gr with
        | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
            let port_type_map =
              If1.all_types_ending_at_no_err_ty expnum in_gr If1.IntMap.empty
            in
            let port_type_map =
              If1.IntMap.filter
                (fun _ tid -> not (If1.is_error_port tid in_gr))
                port_type_map
            in
            If1.IntMap.fold
              (fun ke va retl -> (expnum, ke, va) :: retl)
              port_type_map exp_stack
        | _ -> (expnum, expport, expty) :: exp_stack
      in
      let exp_stack = List.rev exp_stack in
      let res =
        match exp_stack with
        | hd_exp_stack :: tl_exp_stack ->
            ( hd_exp_stack,
              rhs_exps,
              tl_exp_stack,
              in_gr,
              hd_exp_stack :: expl_in_rev )
        | [] -> failwith "This time we need to see a non empty exp_stack"
      in
      res

and do_decldef2 in_gr delc expl_rev decl_rev =
  match delc with
  | Ast.Decldef (lhs_decldef_names, Ast.Exp rhs_decldef_exps) ->
      (* Ast.Decldef:
       First component in a Ast.Decldef is a list of
       lists of declids. Each list is either a
       Ast.Decl_with_type type-spec or Decl_no_type.
       Second component in a Ast.Decldef is
       an exp-list. There is no one-one
       correspondance between each decl
       and each exp. Only after an exp is
       lowered do we have one-one connectivity.
       Note: the grammar for declids_typed builds the list in reverse
       source order; reverse it here to restore correct binding order. *)
      let lhs_decldef_names = List.rev lhs_decldef_names in
      let rev_expl, decl_rev, in_gr =
        do_each_decl2 lhs_decldef_names rhs_decldef_exps [] expl_rev decl_rev
          in_gr
      in
      ((0, 0, 0), rev_expl, decl_rev, in_gr)
  | _ -> raise (If1.Sem_error "Internal compiler error")

and map_names_to_type decls atyp in_gr =
  match decls with
  | current_name :: remaining_names ->
      (* ending let (expnum, expport, ...) *)
      let in_gr =
        match current_name with
        | Ast.Decl_name current_name ->
            let (_, _, typenum), in_gr =
              match atyp with
              | `A atyp -> If1.add_sisal_type in_gr atyp
              | `None ->
                  raise
                    (If1.Sem_error "Require types to be specified in let rec")
            in

            let localsyms, globsyms = in_gr.If1.symtab in
            let localsyms =
              If1.SM.add current_name
                {
                  If1.val_name = current_name;
                  If1.val_ty = typenum;
                  If1.val_def = 0;
                  (* these are unknown at this time *)
                  If1.def_port = 0;
                }
                localsyms
            in
            { in_gr with If1.symtab = (localsyms, globsyms) }
        | Decl_func current_name ->
            let _ =
              match atyp with
              | `A _ ->
                  raise
                    (If1.Sem_error
                       "When writing functions, provide them in a separate let \
                        rec")
              | `None -> ()
            in
            let fn_name, decls, tl =
              match current_name with
              | Ast.Function_header (Ast.Function_name fn_path, decls, tl) ->
                  (String.concat "." fn_path, decls, tl)
              | Ast.Function_header_nodec (Ast.Function_name fn_path, tl) ->
                  (String.concat "." fn_path, [], tl)
            in
            let tyy = extract_types_from_decl_list decls in
            let (_, _, typenum), in_gr =
              If1.add_sisal_type in_gr
                (Ast.Compound_type (Ast.Sisal_function_type (fn_name, tyy, tl)))
            in

            let localsyms, globsyms = in_gr.If1.symtab in
            let localsyms =
              If1.SM.add fn_name
                {
                  If1.val_name = fn_name;
                  If1.val_ty = typenum;
                  If1.val_def = 0;
                  (* these are unknown at this time *)
                  If1.def_port = 0;
                }
                localsyms
            in
            { in_gr with If1.symtab = (localsyms, globsyms) }
      in
      map_names_to_type remaining_names atyp in_gr
  | [] -> in_gr

and add_symbols_before_exp lhs_decl_names in_gr =
  match lhs_decl_names with
  | Ast.Decl_with_type (decls, atype) :: _ ->
      map_names_to_type decls (`A atype) in_gr
  | Ast.Decl_no_type decls :: _ -> map_names_to_type decls `None in_gr
  | (Ast.Decl_tuple_no_type _ | Ast.Decl_tuple_with_type _) :: _ -> in_gr
  | [] -> in_gr

and do_decldef_let_rec_symbols in_gr delc =
  match delc with
  | Ast.Decldef (lhs_decl_names, Ast.Exp _) ->
      (* Ast.Decldef:
       First component in a Ast.Decldef is a list of
       lists of declids. Each list is either a
       Ast.Decl_with_type type-spec or Decl_no_type.

       Second component in a Ast.Decldef is
       an exp-list. There is no one-one
       correspondance between each decl
       and each exp. Only after an exp is
       lowered do we have one-one connectivity. *)
      let in_gr = add_symbols_before_exp lhs_decl_names in_gr in
      in_gr
  | _ -> raise (If1.Sem_error "Internal compiler error")

and do_decldef_let_rec in_gr delc expl_rev decl_rev =
  match delc with
  | Ast.Decldef (lhs_decldef_names, Ast.Exp rhs_decldef_exps) ->
      (* Ast.Decldef:
       First component in a Ast.Decldef is a list of
       lists of declids. Each list is either a
       Ast.Decl_with_type type-spec or Decl_no_type.

       Second component in a Ast.Decldef is
       an exp-list. There is no one-one
       correspondance between each decl
       and each exp. Only after an exp is
       lowered do we have one-one connectivity. *)
      let rev_expl, decl_rev, in_gr =
        do_each_decl2 lhs_decldef_names rhs_decldef_exps [] expl_rev decl_rev
          in_gr
      in
      ((0, 0, 0), rev_expl, decl_rev, in_gr)
  | _ -> raise (If1.Sem_error "Internal compiler error")

and do_function_name in_gr = function
  | Ast.Function_name _ ->
      (* what do we do with the function names *)
      ((0, 0, 0), in_gr)

and do_arg in_gr = function Ast.Arg e -> do_exp in_gr e

and find_an_union_ty iiee in_gr =
  let tmn = If1.get_typemap_tm in_gr in
  match If1.TM.find_opt iiee tmn with
  | Some (If1.Union (lt, _, _)) -> lt
  | _ -> failwith "If1.Union type expected"

and enumerate_union_tags iiee in_gr =
  let tmn = If1.get_typemap_tm in_gr in
  let rec lookup_tags mmm tmn tag_l =
    match If1.TM.find_opt mmm tmn with
    | Some (If1.Union (_, nxt, _)) ->
        if nxt = 0 then mmm :: tag_l else lookup_tags nxt tmn (mmm :: tag_l)
    | _ -> failwith "If1.Union type expected"
  in
  lookup_tags iiee tmn []

and find_matching_union_str eee tm =
  If1.TM.fold
    (fun k v z ->
      match z with
      | If1.Emp -> (
          match v with
          | If1.Union (_, _, xx) -> (
              match String.equal xx eee with true -> If1.Som k | false -> z)
          | _ -> z)
      | _ -> z)
    tm If1.Emp

and get_new_tagcase_graph in_gr vntt e =
  let tagcase_gr_n = If1.get_a_new_graph in_gr in
  let cs, ps = tagcase_gr_n.If1.symtab in
  (* We can only add the tagcase If1.Name
      to matched variants. Otherwise
      cannot have access to the union's
      contents at all. So do not add
      the value name to Otherwise. *)
  let in_gr_ =
    match vntt with
    | `AnyTag (vn_n, uniontt, _) ->
        {
          tagcase_gr_n with
          If1.symtab =
            ( If1.SM.add vn_n
                {
                  If1.val_name = vn_n;
                  If1.val_ty = uniontt;
                  If1.val_def = 0;
                  If1.def_port = 0;
                }
                cs,
              ps );
        }
    | `OtherwiseTag -> tagcase_gr_n
  in
  (* There may be an expression list
      returning multiple values in the
      RHS of the variant. Add them the
      way we usually do to the subgraph. *)
  let outs_, in_gr_ = do_exp in_gr_ e in
  let in_gr_ =
    If1.connect_one_to_one (If1.all_nodes_joining_at outs_ in_gr_) 0 in_gr_
  in

  (* Add some pragmas -- this may need
      to match what the Sisal developers
      liked to have here -- *)
  let prags_sth =
    match vntt with
    | `AnyTag (_, _, bii) ->
        [
          If1.Name (List.fold_right (fun x y -> If1.cate_nicer x y ",") bii "");
        ]
    | `OtherwiseTag -> [ If1.Name "Otherwise" ]
  in
  (* return the output types in jj,
      pragmas and updated graph likewise *)
  (outs_, prags_sth, in_gr_)

(* Helper to strip Monad/Error edges from the comparison map *)
and filter_data_types in_gr ty_map =
  let filtered =
    If1.IntMap.filter
      (fun _ ty_id -> not (If1.is_error_port ty_id in_gr))
      ty_map
  in
  If1.IntMap.fold
    (fun ke ty_id out_map ->
      if If1.is_typed_error_ty ty_id in_gr then
        If1.IntMap.add ke (If1.type_of_error_ty ty_id in_gr) out_map
      else If1.IntMap.add ke ty_id out_map)
    filtered If1.IntMap.empty

and check_subgr_tys in_gr msg jj prev =
  (* 1. Strip the Railway edges *)
  let jj_data = filter_data_types in_gr jj in
  let prev_data = filter_data_types in_gr prev in

  (* 2. Fast Arity Check: Do they have the same number of pure data ports? *)
  if If1.IntMap.cardinal jj_data <> If1.IntMap.cardinal prev_data then
    raise
      (If1.Sem_error
         (Printf.sprintf
            "Data Arity Mismatch: Branch outputs do not align AT %s" msg))
  else
    (* 3. Extract the ordered types (ignoring the now-gappy port numbers) *)
    let jj_types = List.map snd (If1.IntMap.bindings jj_data) in
    let prev_types = List.map snd (If1.IntMap.bindings prev_data) in

    (* 4. Compare the sequences directly *)
    List.iter2
      (fun exp act ->
        if exp <> act then
          let tm = If1.get_typemap_tm in_gr in
          match (If1.TM.find_opt exp tm, If1.TM.find_opt act tm) with
          | Some ty_exp, Some ty_act ->
              if not (If1.structurally_equal in_gr [] ty_exp ty_act) then
                (* Check if the mismatch is due to an unexpected Error Type *)
                let err_msg =
                  match ty_act with
                  | ERROR s -> Printf.sprintf "Hardware Trap/Error found: %s" s
                  | _ ->
                      Printf.sprintf
                        "Type error: Expected %s (#%d), but found %s (#%d)"
                        (If1.printable_full_type (If1.get_typemap_tm in_gr) exp)
                        exp
                        (If1.printable_full_type (If1.get_typemap_tm in_gr) act)
                        act
                in
                failwith ("Type Mismatch: " ^ err_msg)
          | _ -> failwith "Verification Error: Typemap resolution failed")
      jj_types prev_types

and boundary_node_lookup in_gr =
  let pe = in_gr.If1.eset in
  let ps = snd in_gr.If1.symtab in
  let in_lists =
    If1.ES.fold
      (fun ((x, p), (_, _), _) y -> if x = 0 then (x, p) :: y else y)
      pe []
  in
  let str_names =
    let zzz = If1.AStrSet.empty in
    List.fold_right
      (fun (x, p) z ->
        If1.SM.fold
          (fun _
               {
                 If1.val_ty = _;
                 If1.val_name = str;
                 If1.val_def = jj;
                 If1.def_port = jp;
               } z1 -> if jj = x && jp = p then If1.AStrSet.add str z1 else z1)
          ps z)
      in_lists zzz
  in
  str_names

and if_type_fail in_gr jj prev =
  raise
    (If1.Sem_error
       (print_endline (If1.string_of_graph in_gr);
        let k =
          "OUTPUT TYPES OF SELECT DO NOT MATCH: " ^ " ["
          ^ If1.cate_list
              (List.map
                 (fun x -> string_of_int x ^ ":" ^ If1.rev_lookup_ty_name x)
                 prev)
              ";"
          ^ "] ["
          ^ If1.cate_list
              (List.map
                 (fun x -> string_of_int x ^ ":" ^ If1.rev_lookup_ty_name x)
                 jj)
              ""
          ^ "]"
        in
        print_endline k;
        k))

and new_graph_for_tag_case vn_n t1 in_gr =
  (* Put local symbols of the incoming graph
      into the parent If1.symtab to initialize
      a new graph. *)
  let tagcase_gr_ = If1.get_symtab_for_new_scope in_gr in

  let cs, ps = tagcase_gr_.symtab in
  let tmm = tagcase_gr_.typemap in

  let a_new_gr = If1.get_a_new_graph tagcase_gr_ in
  (* add the tagcase's variable name, for example:
      tagcase "P", add P *)
  (* need a new graph here in a compound node *)
  let cs =
    If1.SM.add vn_n
      {
        If1.val_name = vn_n;
        If1.val_ty = t1;
        If1.val_def = 0;
        If1.def_port = 0;
      }
      cs
  in
  { a_new_gr with If1.symtab = (cs, ps); If1.typemap = tmm }

and lookup_tag_nums tagn tm outs =
  match tagn with
  | [] -> outs
  | hdt :: tlt ->
      let looked_up_num hdt tm =
        match find_matching_union_str hdt tm with
        | If1.Emp ->
            raise (If1.Node_not_found "Unknown tag type in an If1.union")
        | If1.Som k -> k
      in
      lookup_tag_nums tlt tm (looked_up_num hdt tm :: outs)

and tag_typecheck_fail vn_n in_gr jj prev =
  raise
    (If1.Sem_error
       (print_endline (If1.string_of_graph in_gr);
        let k =
          "OUTPUT TYPES OF TAGS DO NOT MATCH FOR: " ^ vn_n ^ " ["
          ^ If1.cate_list
              (List.map
                 (fun x -> string_of_int x ^ ":" ^ If1.rev_lookup_ty_name x)
                 prev)
              ";"
          ^ "] ["
          ^ If1.cate_list
              (List.map
                 (fun x -> string_of_int x ^ ":" ^ If1.rev_lookup_ty_name x)
                 jj)
              ""
          ^ "]"
        in
        print_endline k;
        k))

and check_tag_types vn_n jj prev in_gr =
  if jj = prev then true
  else
    let name_it_prev =
      If1.IntMap.fold
        (fun _ ed_ty out_str ->
          If1.printable_full_type (If1.get_typemap_tm in_gr) ed_ty
          ^ "; " ^ out_str)
        prev ""
    in
    let name_it_jj =
      If1.IntMap.fold
        (fun _ ed_ty out_str ->
          If1.printable_full_type (If1.get_typemap_tm in_gr) ed_ty
          ^ "; " ^ out_str)
        jj ""
    in
    raise
      (let stack = Printexc.get_callstack 5 in
       (* Capture top 5 frames *)
       (*If1.dump_typemap tm;*)
       print_endline (Printexc.raw_backtrace_to_string stack);
       If1.If1_View.export_debug_html "CRASHED.html" in_gr;
       If1.Sem_error
         ("Output types do not match for:" ^ name_it_jj ^ ", " ^ vn_n ^ ", "
        ^ name_it_prev))

and tag_builder t1 in_gr tagcase_g ex vn_n prev_out_types tag_gr_map =
  (* A recursive visitor that builds subgraphs for each variant
      in the match. *)
  match ex with
  | [] -> (prev_out_types, tagcase_g, tag_gr_map)
  | hde :: tl ->
      let tagcase_gr_ = new_graph_for_tag_case vn_n t1 in_gr in
      let jj, prags, tagcase_gr_i, nums =
        match hde with
        | Ast.Tag_list (Tagnames tns, e) ->
            let tm = If1.get_typemap_tm tagcase_g in
            let nums = lookup_tag_nums tns tm [] in
            (* tag labels that are being matched *)
            let a_tag_ty =
              find_an_union_ty
                (try List.hd nums
                 with _ -> raise (If1.Sem_error "error lowering tag_case"))
                tagcase_g
            in
            (* the output types from each variant is put
            in jj below ---
            all tags need to output the same types--- *)
            let outlis, prags, in_gt_ =
              get_new_tagcase_graph tagcase_gr_
                (`AnyTag (vn_n, a_tag_ty, tns))
                e
            in
            let jj, in_gt_ = extr_types in_gt_ (outlis, If1.IntMap.empty) in
            (jj, prags, in_gt_, nums)
      in
      (* There can be a bunch of exps from each tag,
        get the types and compare
        them to make sure that they are the same
        as for each earlier tag-case match *)
      let _ =
        if If1.IntMap.is_empty prev_out_types then true
        else check_tag_types vn_n jj prev_out_types tagcase_gr_
      in
      let (ii, _, _), tagcase_g =
        If1.add_node_2
          (`Compound (tagcase_gr_i, If1.INTERNAL, 0, prags, []))
          tagcase_g
      in
      let tagcase_g = add_edges_to_boundary tagcase_gr_i tagcase_g ii in
      (* map each tagnum to its subgraph,
        this will become the association list *)
      let tag_gr_map =
        List.fold_right (fun c mm -> If1.IntMap.add c ii mm) nums tag_gr_map
      in
      tag_builder t1 in_gr tagcase_g tl vn_n jj tag_gr_map

and add_edges_from_inner_to_outer ty_map outer_gr comp_node namen =
  (* Propagate outputs of inner compound nodes to the
      recursive caller, using If1.MULTIARITY. Make sure that they
      are returned in the expected order.*)
  let in_port_1 =
    let in_array = Array.make (If1.IntMap.cardinal ty_map) "" in
    in_array
  in
  let out_port_1 =
    let out_array = Array.make (If1.IntMap.cardinal ty_map) "" in
    out_array
  in
  let (oo, op, ot), outer_gr =
    If1.add_node_2
      (`Simple (If1.MULTIARITY, in_port_1, out_port_1, [ If1.Name namen ]))
      outer_gr
  in
  let outer_gr =
    If1.IntMap.fold
      (fun ke ed_ty out_gr -> If1.add_edge comp_node ke oo ke ed_ty out_gr)
      ty_map outer_gr
  in
  ((oo, op, ot), outer_gr)

and add_edges_to_boundary a_gr outer_gr to_node =
  let bound_nodes_a = boundary_node_lookup a_gr in
  let bound_nodes_a_lis =
    If1.AStrSet.fold (fun x y -> x :: y) bound_nodes_a []
  in
  let sym_ids =
    List.map
      (fun x ->
        let xx, _ = If1.get_symbol_id x a_gr in
        xx)
      bound_nodes_a_lis
  in
  let gr, _ =
    List.fold_right
      (fun (nx, np, nt) (y, i) -> (If1.add_edge nx np to_node i nt y, i + 1))
      sym_ids (outer_gr, 0)
  in
  gr

and get_simple_unary nou in_gr node_tag =
  let (z, _, _), in_gr =
    let in_port_1 =
      let in_array = Array.make 1 "" in
      in_array
    in
    let out_port_1 =
      let out_array = Array.make nou "" in
      out_array
    in
    If1.add_node_2
      (`Simple (node_tag, in_port_1, out_port_1, [ If1.No_pragma ]))
      in_gr
  in
  ((z, 0, 0), in_gr)

and unary_internal nou e pi t1 in_gr node_tag =
  let (z, _, _), in_gr = get_simple_unary nou in_gr node_tag in
  let in_gr = If1.add_edge e pi z 0 t1 in_gr in
  ((z, 0, t1), in_gr)

and unary_exp nou in_gr e node_tag =
  let (e, pi, t1), in_gr = do_simple_exp in_gr e in
  unary_internal nou e pi t1 in_gr node_tag

(* Insert a TYPECAST node to coerce node (src, sp) from src_ty to tgt_ty. *)
and insert_typecast src sp src_ty tgt_ty in_gr =
  let (cast_n, _, _), in_gr =
    If1.add_node_2
      (`Simple
         (If1.TYPECAST, Array.make 1 "", Array.make 1 "", [ If1.No_pragma ]))
      in_gr
  in
  let in_gr = If1.add_edge src sp cast_n 0 src_ty in_gr in
  ((cast_n, 0, tgt_ty), in_gr)

(* Numeric type rank for widening coercion: higher = wider.
   Returns None if the type is not a widening-eligible numeric type. *)
and numeric_rank ty in_gr =
  match If1.lookup_ty_safe ty in_gr with
  | Some (If1.Basic If1.INTEGRAL) -> Some 10
  | Some (If1.Basic If1.SHORT) -> Some 8
  | Some (If1.Basic If1.LONG) -> Some 20
  | Some (If1.Basic If1.REAL) -> Some 30
  | Some (If1.Basic If1.DOUBLE) -> Some 40
  | _ -> None

(* Try to coerce (src, sp, src_ty) to tgt_ty if they are compatible
   numeric types; otherwise return the triple unchanged. *)
and maybe_coerce src sp src_ty tgt_ty in_gr =
  if src_ty = tgt_ty then ((src, sp, src_ty), in_gr)
  else
    match (numeric_rank src_ty in_gr, numeric_rank tgt_ty in_gr) with
    | Some r1, Some r2 when r1 < r2 ->
        insert_typecast src sp src_ty tgt_ty in_gr
    | _ -> ((src, sp, src_ty), in_gr)

and bin_exp a b in_gr node_tag =
  let get_simple_bin in_gr node_tag =
    let in_port_2 =
      let in_array = Array.make 2 "" in
      in_array
    in
    let out_port_1 =
      let out_array = Array.make 1 "" in
      out_array
    in
    If1.add_node_2
      (`Simple (node_tag, in_port_2, out_port_1, [ If1.No_pragma ]))
      in_gr
  in
  let base_case_bin a b node_tag in_gr =
    let (c, pi1, qq1), i_gr = do_simple_exp in_gr a in
    let (d, pi2, qq2), i_gr = do_simple_exp i_gr b in
    let (z, _, _), out_gr = get_simple_bin i_gr node_tag in
    let c, pi1, qq1 =
      match If1.get_node c i_gr with
      | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
          first_incoming_triple_to_multiarity c i_gr
      | _ -> (c, pi1, qq1)
    in
    let d, pi2, qq2 =
      match If1.get_node d i_gr with
      | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
          first_incoming_triple_to_multiarity d i_gr
      | _ -> (d, pi2, qq2)
    in
    (* Determine common type, widening if needed *)
    let (c, pi1, qq1), (d, pi2, qq2), common_ty, out_gr =
      if qq1 = qq2 then ((c, pi1, qq1), (d, pi2, qq2), qq1, out_gr)
      else
        match (numeric_rank qq1 out_gr, numeric_rank qq2 out_gr) with
        | Some r1, Some r2 ->
            if r1 < r2 then
              let (c, pi1, qq1), out_gr =
                insert_typecast c pi1 qq1 qq2 out_gr
              in
              ((c, pi1, qq1), (d, pi2, qq2), qq2, out_gr)
            else if r2 < r1 then
              let (d, pi2, qq2), out_gr =
                insert_typecast d pi2 qq2 qq1 out_gr
              in
              ((c, pi1, qq1), (d, pi2, qq2), qq1, out_gr)
            else ((c, pi1, qq1), (d, pi2, qq2), qq1, out_gr)
        | _ ->
            raise
              (If1.Sem_error
                 (let _ =
                    let kkk =
                      If1.cate_list
                        [
                          Ast.str_simple_exp ~offset:2 a;
                          " of type:" ^ string_of_int qq1 ^ " maps to "
                          ^ If1.p_f_t in_gr qq1;
                          Ast.str_simple_exp ~offset:2 b;
                          " of type:" ^ string_of_int qq2 ^ " maps to "
                          ^ If1.p_f_t in_gr qq2;
                        ]
                        "\n"
                    in
                    print_endline kkk
                  in
                  "ERROR: Bad type in binary exp---"))
    in
    let out_gr = If1.add_edge c pi1 z 0 common_ty out_gr in
    let out_gr = If1.add_edge d pi2 z 1 common_ty out_gr in
    ((z, 0, common_ty), out_gr)
  in
  base_case_bin a b node_tag in_gr

and organize_ret_info return_action_list mask_ty_list =
  let return_action_list, port_remap, cou =
    List.fold_right
      (fun (y, x, tt) (outL, port_remap, cou) ->
        if If1.IntMap.mem x port_remap = true then
          ((y, tt, If1.IntMap.find x port_remap) :: outL, port_remap, cou)
        else ((y, tt, cou) :: outL, If1.IntMap.add x cou port_remap, cou + 1))
      return_action_list ([], If1.IntMap.empty, 1)
  in

  (* TODO -> GO HERE NEED TO ADD THIS TO THE OTHER LOOPS *)
  let mask_ty_list, _, _ =
    List.fold_right
      (fun rrr (outL, port_remap, cou) ->
        match rrr with
        | Some (x, _, tt) ->
            if If1.IntMap.mem x port_remap = true then
              (Some (tt, If1.IntMap.find x port_remap) :: outL, port_remap, cou)
            else
              (Some (tt, cou) :: outL, If1.IntMap.add x cou port_remap, cou + 1)
        | None -> (None :: outL, port_remap, cou))
      mask_ty_list ([], port_remap, cou)
  in
  (return_action_list, mask_ty_list)

and add_ret in_gr return_action_list mask_ty_list prag =
  (* Build Return-Signature To Provide To Outer
           Loop In Ord  er To Build Its Returns Graph. *)
  let return_action_list, mask_ty_list =
    organize_ret_info return_action_list mask_ty_list
  in
  let for_gr = If1.get_a_new_graph in_gr in
  add_return_gr for_gr in_gr return_action_list mask_ty_list prag

and point_edges_to_boundary frm elp elt in_gr =
  (* all edges ending at frm now to end at Boundary *)
  match If1.get_node frm in_gr with
  | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
      (*In case frm is a If1.MULTIARITY, redirect
      incoming edges to the boundary node.*)
      let pe = in_gr.If1.eset in
      let unwanted_edges = If1.all_edges_ending_at frm in_gr in
      let nes = pe in
      let start_in_port_for_boundary =
        If1.ES.cardinal
          (If1.filter_data_edges in_gr (If1.all_edges_ending_at 0 in_gr))
      in
      to_if1_msg 4
        "point_edges_to_boundary: MULTIARITY node=%d, start_port=%d, %d edges \
         to redirect"
        frm start_in_port_for_boundary
        (If1.ES.cardinal unwanted_edges);
      let red_nes, _ =
        If1.redirect_edges 0 (* 0 is Boundary *)
          unwanted_edges start_in_port_for_boundary
      in
      to_if1_msg 4 "point_edges_to_boundary: redirected edges: [%s]"
        (String.concat "; "
           (List.map
              (fun ((n1, p1), (n2, p2), _) ->
                Printf.sprintf "%d:%d->%d:%d" n1 p1 n2 p2)
              (If1.ES.elements red_nes)));
      let nes = If1.ES.union nes red_nes in
      { in_gr with If1.eset = nes }
  | _ ->
      (* 3. Get the actual edges reaching the boundary node (ID 0) *)
      (* Only edges with non-ERROR types are treated as logical returns *)
      let start_port_num =
        If1.ES.cardinal
          (If1.filter_data_edges in_gr (If1.all_edges_ending_at 0 in_gr))
      in
      If1.add_edge frm elp 0 start_port_num elt in_gr

and create_bool_bin_op a b in_gr op =
  let (nod_num, nod_po, _), in_gr = bin_exp a b in_gr op in
  (*Return 1 for If1.BOOLEAN TYPE*)
  ((nod_num, nod_po, If1.lookup_tyid If1.BOOLEAN), in_gr)

and create_bool_unary_op nou a in_gr op =
  let (nod_num, nod_po, _), in_gr = unary_exp nou a in_gr op in
  ((nod_num, nod_po, If1.lookup_tyid If1.BOOLEAN), in_gr)

and do_simple_exp in_gr in_sim_ex =
  match in_sim_ex with
  | Constant x -> do_constant in_gr x
  | Negate e -> unary_exp 1 in_gr e NEGATE
  | Pipe (a, b) -> bin_exp a b in_gr ACATENATE
  | Divide (left, right) ->
      let (div_node, div_port, div_ty), in_gr =
        bin_exp left right in_gr If1.FDIVIDE
      in
      let opcode =
        let incoming_type = If1.lookup_ty div_ty in_gr in
        if If1.is_real_type incoming_type = true then If1.FDIVIDE
        else if If1.is_integral_type incoming_type = true then If1.IDIVIDE
        else failwith "Only integral or real valued types can be divided"
      in
      let nmap_update =
        match If1.get_node div_node in_gr with
        | Simple (lab, _, pin, pout, prag) ->
            If1.NM.add div_node
              (If1.Simple (lab, opcode, pin, pout, prag))
              in_gr.nmap
        | _ -> failwith "Error looking up divide operation"
      in
      let in_gr = { in_gr with nmap = nmap_update } in

      (* 3. Register the "DIV0" Error Type in the Typemap *)
      let (_, _, err_ty_id), in_gr =
        If1.add_sisal_type in_gr (Ast.Error_ty "DIV0")
      in

      (* 4. The Railroad Wiring: Append port to Boundary's 3rd list and wire it *)
      let in_gr =
        match If1.get_node_map in_gr |> If1.NM.find 0 with
        | If1.Boundary (ins, outs, errs, prags) ->
            let next_err_port = List.length errs + 1 in

            (* Update Boundary with the new error-return slot *)
            let in_gr =
              {
                in_gr with
                nmap =
                  If1.NM.add 0
                    (If1.Boundary
                       (ins, outs, errs @ [ (div_node, err_ty_id) ], prags))
                    in_gr.nmap;
              }
            in

            (* Wire the Railroad Edge: Src:Port2 -> Boundary:next_err_port *)
            If1.add_edge div_node 2 0 next_err_port err_ty_id in_gr
        | _ -> in_gr
      in
      ((div_node, div_port, div_ty), in_gr)
  | Lambda (header, e) ->
      (* Build an anonymous subgraph exactly like do_internals/Function_single,
         but with no name.  The caller (decldef machinery) will bind the
         resulting compound node to the lval name. *)
      let (_, _, fn_ty), new_fun_gr =
        do_function_header
          (If1.inherit_parent_syms in_gr (If1.get_a_new_graph in_gr))
          header
      in
      (* Count how many boundary ports are declared parameters.
         Any ports added beyond this count during body lowering are captures. *)
      let n_params = If1.boundary_in_port_count new_fun_gr in
      let new_fun_gr =
        let (frm, elp, elt), new_fun_gr = do_exp new_fun_gr e in
        point_edges_to_boundary frm elp elt new_fun_gr
      in
      let new_fun_gr = If1.graph_clean_multiarity new_fun_gr in
      verify_function_returns "<lambda>" fn_ty new_fun_gr;
      let (lam_node, lam_port, _), in_gr =
        If1.add_node_2
          (`Compound (new_fun_gr, If1.INTERNAL, 0, [ If1.Name "<lambda>" ], []))
          in_gr
      in
      (* Wire captured variables: for each boundary input port added beyond the
         declared parameters, add an edge from the outer scope's value into the
         lambda compound node at that port. *)
      let in_gr =
        List.fold_left
          (fun in_gr (_, cap_port, cap_name) ->
            if cap_port < n_params then in_gr
            else
              let (src_n, src_p, src_ty), in_gr =
                If1.get_symbol_id cap_name in_gr
              in
              If1.add_edge src_n src_p lam_node cap_port src_ty in_gr)
          in_gr
          (If1.get_named_input_ports new_fun_gr)
      in
      ((lam_node, lam_port, fn_ty), in_gr)
  | Pos ((line, col), inner_exp) ->
      current_src_pos := (line, col);
      let (n, p, ty), in_gr = do_simple_exp in_gr inner_exp in
      let in_gr = If1.set_node_srcline n line col in_gr in
      ((n, p, ty), in_gr)
  | Multiply (a, b) ->
      (* Lower both sides first to check their types *)
      let (an, ap, at), in_gr = do_simple_exp in_gr a in
      let (bn, bp, bt), in_gr = do_simple_exp in_gr b in
      (* Unwrap MULTIARITY nodes (e.g. for-loop results) to get actual type *)
      let an, ap, at =
        match If1.get_node an in_gr with
        | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
            first_incoming_triple_to_multiarity an in_gr
        | _ -> (an, ap, at)
      in
      let bn, bp, bt =
        match If1.get_node bn in_gr with
        | If1.Simple (_, If1.MULTIARITY, _, _, _) ->
            first_incoming_triple_to_multiarity bn in_gr
        | _ -> (bn, bp, bt)
      in
      let a_ty = If1.lookup_ty at in_gr in
      let b_ty = If1.lookup_ty bt in_gr in
      (match (If1.is_mat_type a_ty, If1.is_vector_type a_ty,
              If1.is_mat_type b_ty, If1.is_vector_type b_ty) with
      | true, _, true, _ ->
          (* mat * mat → MATMUL, result is same mat type *)
          let (mn, mp, _), in_gr =
            If1.add_node_2
              (`Simple (If1.MATMUL, [| ""; "" |], [| "" |], [])) in_gr
          in
          let in_gr = If1.add_edge an ap mn 0 at in_gr in
          let in_gr = If1.add_edge bn bp mn 1 bt in_gr in
          ((mn, mp, at), in_gr)
      | true, _, false, true ->
          (* mat * vec → MATVECMUL, result is the vec type *)
          let (mn, mp, _), in_gr =
            If1.add_node_2
              (`Simple (If1.MATVECMUL, [| ""; "" |], [| "" |], [])) in_gr
          in
          let in_gr = If1.add_edge an ap mn 0 at in_gr in
          let in_gr = If1.add_edge bn bp mn 1 bt in_gr in
          ((mn, mp, bt), in_gr)
      | false, true, true, _ ->
          (* vec * mat → VECMATMUL, result is the vec type *)
          let (mn, mp, _), in_gr =
            If1.add_node_2
              (`Simple (If1.VECMATMUL, [| ""; "" |], [| "" |], [])) in_gr
          in
          let in_gr = If1.add_edge an ap mn 0 at in_gr in
          let in_gr = If1.add_edge bn bp mn 1 bt in_gr in
          ((mn, mp, at), in_gr)
      | _ ->
          (* scalar * scalar (or vec * vec element-wise) → TIMES *)
          let (tn, tp, _), in_gr =
            If1.add_node_2
              (`Simple (If1.TIMES, [| ""; "" |], [| "" |], [])) in_gr
          in
          let common_ty = at in
          let in_gr = If1.add_edge an ap tn 0 common_ty in_gr in
          let in_gr = If1.add_edge bn bp tn 1 common_ty in_gr in
          ((tn, tp, common_ty), in_gr))
  | Subtract (a, b) -> bin_exp a b in_gr SUBTRACT
  | Add (a, b) -> bin_exp a b in_gr ADD
  | Shl (a, b) -> bin_exp a b in_gr SHL
  | Shr (a, b) -> bin_exp a b in_gr SHR
  | And (a, b) -> bin_exp a b in_gr AND
  | Or (a, b) -> bin_exp a b in_gr OR
  | Not e -> unary_exp 1 in_gr e NOT
  | Not_equal (a, b) -> create_bool_bin_op a b in_gr NOT_EQUAL
  | Equal (a, b) -> create_bool_bin_op a b in_gr EQUAL
  | Lesser_equal (a, b) -> create_bool_bin_op a b in_gr LESSER_EQUAL
  | Lesser (a, b) -> create_bool_bin_op a b in_gr LESSER
  | Greater_equal (a, b) -> create_bool_bin_op a b in_gr GREATER_EQUAL
  | Greater (a, b) -> create_bool_bin_op a b in_gr GREATER
  | Vec (vect, el) ->
      (* 1. Determine expected width from the AST type *)
      let expected_len = Ast.get_vec_len vect in
      (* Ensure this helper exists in Ast *)
      let actual_len = List.length el in

      (* 2. Validate: Must be 1 (Splat) or exactly the Vector Width (Build) *)
      if actual_len <> 1 && actual_len <> expected_len then
        failwith
          (Printf.sprintf "Type Error: %s expects 1 or %d args, got %d"
             (Ast.str_vec_type vect) expected_len actual_len);

      (* 3. Process elements into ports *)
      let ports_info, in_gr =
        List.fold_left
          (fun (acc, g) e ->
            let p, g' = do_exp g e in
            (p :: acc, g'))
          ([], in_gr) el
      in
      let ports_info = List.rev ports_info in

      (* 4. Determine Opcode *)
      let opcode = if actual_len = 1 then If1.VSPLAT else If1.VBUILD in

      (* 5. Create Node and Edges *)
      let (vn, vp, _), in_gr =
        If1.add_node_2
          (`Simple
             ( opcode,
               Array.make (List.length ports_info) "",
               Array.make 1 "",
               [ If1.No_pragma ] ))
          in_gr
      in
      let vt = If1.lookup_tyid (If1.ast_if1_type vect) in
      let in_gr =
        List.fold_left2
          (fun g i (en, ep, et) -> If1.add_edge en ep vn i et g)
          in_gr
          (List.init (List.length ports_info) (fun x -> x))
          ports_info
      in
      ((vn, vp, vt), in_gr)
  | Mat (mat_t, el) ->
      (* 1. Determine dimension (e.g., Mat2 -> 2, so 4 elements total) *)
      let dim = Ast.get_mat_dim mat_t in
      let expected_len = dim * dim in
      let actual_len = List.length el in

      (* 2. Validate: 1 (splat), dim (row vectors), or dim*dim (flat scalars) *)
      if actual_len <> 1 && actual_len <> dim && actual_len <> expected_len then
        raise
          (If1.Sem_error
             (Printf.sprintf "Type Error: %s expects 1, %d (rows), or %d args, got %d"
                (Ast.str_mat_type mat_t) dim expected_len actual_len));

      (* 3. Lower all argument expressions *)
      let ports_info, in_gr =
        List.fold_left
          (fun (acc, g) e ->
            let p, g' = do_exp g e in
            (p :: acc, g'))
          ([], in_gr) el
      in
      let ports_info = List.rev ports_info in

      (* 3b. If row-vector mode, expand each float-N row into dim scalar ports *)
      let ports_info, in_gr =
        if actual_len = dim then
          List.fold_right
            (fun row_triple (acc, g) ->
              let scalars, g = extract_vec_components row_triple dim g in
              (scalars @ acc, g))
            ports_info ([], in_gr)
        else (ports_info, in_gr)
      in

      (* 4. Opcode (MATSPLAT vs MATBUILD) *)
      let opcode = if actual_len = 1 then If1.MATSPLAT else If1.MATBUILD in

      (* 5. Create Node and Edges *)
      let (mn, mp, _), in_gr =
        If1.add_node_2
          (`Simple
             ( opcode,
               Array.make (List.length ports_info) "",
               Array.make 1 "",
               [ If1.No_pragma ] ))
          in_gr
      in
      let mt = If1.lookup_tyid (If1.ast_mat_if1_type mat_t) in
      let in_gr =
        List.fold_left2
          (fun g i (en, ep, et) -> If1.add_edge en ep mn i et g)
          in_gr
          (List.init (List.length ports_info) (fun x -> x))
          ports_info
      in

      ((mn, mp, mt), in_gr)
  | Invocation (Ast.Function_name fn, arg) -> (
      let deref_fn = String.concat "." fn in
      match deref_fn with
      (*TODO: More libs *)
      | "ACREATE"
        when let cs, ps = in_gr.If1.symtab in
             not (If1.SM.mem "ACREATE" cs || If1.SM.mem "ACREATE" ps) ->
          let in_port_00 = Array.make 1 "" in
          let out_port_00 = Array.make 1 "" in
          let (n, p, _), in_gr =
            If1.add_node_2
              (`Simple (If1.ACREATE, in_port_00, out_port_00, []))
              in_gr
          in
          let (_, _, arr_typ), in_gr =
            If1.add_compound_type in_gr (Ast.Sisal_array Ast.Null)
          in
          ((n, p, arr_typ), in_gr)
      | ("ARRAY_ADDH" | "ARRAY_ADDL") as array_addx ->
          let (n, _, _), in_gr =
            let in_port_00 = Array.make 1 "" in
            let out_port_00 = Array.make 1 "" in
            If1.add_node_2
              (`Simple
                 ( (match array_addx with
                   | "ARRAY_ADDH" -> If1.AADDH
                   | _ -> If1.AADDL),
                   in_port_00,
                   out_port_00,
                   [] ))
              in_gr
          in
          let tt, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp [ fst_exp; last_exp ] ->
                    let (l, m, tt), in_gr = do_simple_exp in_gr fst_exp in
                    let (ii, jj, pp), in_gr = do_simple_exp in_gr last_exp in
                    let in_gr = If1.add_edge l m n 0 tt in_gr in
                    let in_gr = If1.add_edge ii jj n 1 pp in_gr in
                    (tt, in_gr)
                | _ ->
                    raise
                      (If1.Sem_error ("Incorrect usage" ^ " for " ^ array_addx))
                )
          in
          ((n, 0, tt), in_gr)
      | "ARRAY_LIMH" ->
          let (n, _, _), in_gr =
            let in_port_00 = Array.make 1 "" in
            let out_port_00 = Array.make 1 "" in
            If1.add_node_2
              (`Simple (If1.ALIMH, in_port_00, out_port_00, []))
              in_gr
          in
          let _, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps ->
                    List.fold_right
                      (fun x (cou, in_gr) ->
                        let (l, m, tt), in_gr = do_simple_exp in_gr x in
                        (cou + 1, If1.add_edge l m n cou tt in_gr))
                      aexps (0, in_gr)
                | _ -> (0, in_gr))
          in
          ((n, 0, If1.lookup_tyid INTEGRAL), in_gr)
      | "ARRAY_ADJUST" ->
          let in_port_00 = Array.make 3 "" in
          let out_port_00 = Array.make 1 "" in
          let (n, _, _), in_gr =
            If1.add_node_2
              (`Simple (If1.AADJUST, in_port_00, out_port_00, []))
              in_gr
          in
          let _, in_gr, type_lis =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps ->
                    List.fold_right
                      (fun x (cou, in_gr, pa) ->
                        let (l, m, tt), in_gr = do_simple_exp in_gr x in
                        (cou + 1, If1.add_edge l m n cou tt in_gr, tt :: pa))
                      aexps (0, in_gr, [])
                | _ -> (0, in_gr, []))
          in
          ((n, 0, List.hd type_lis), in_gr)
      | "ARRAY_LIML" ->
          let in_port_00 = Array.make 1 "" in
          let out_port_00 = Array.make 1 "" in
          let (n, _, _), in_gr =
            If1.add_node_2
              (`Simple (If1.ALIML, in_port_00, out_port_00, []))
              in_gr
          in
          let _, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps ->
                    List.fold_right
                      (fun x (cou, in_gr) ->
                        let (l, m, tt), in_gr = do_simple_exp in_gr x in
                        (cou + 1, If1.add_edge l m n cou tt in_gr))
                      aexps (0, in_gr)
                | _ -> (0, in_gr))
          in
          ((n, 0, If1.lookup_tyid INTEGRAL), in_gr)
      | ("ARRAY_REML" | "ARRAY_REMH") as array_remx ->
          let (n, _, _), in_gr =
            If1.add_node_2
              (`Simple
                 ( (match array_remx with
                   | "ARRAY_REML" -> If1.AREML
                   | _ -> If1.AREMH),
                   Array.make 1 "",
                   Array.make 1 "",
                   [] ))
              in_gr
          in
          let arr_ty, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp [ arr_exp ] ->
                    let (l, m, tt), in_gr = do_simple_exp in_gr arr_exp in
                    let in_gr = If1.add_edge l m n 0 tt in_gr in
                    (tt, in_gr)
                | _ ->
                    raise (If1.Sem_error ("Incorrect usage for " ^ array_remx)))
          in
          ((n, 0, arr_ty), in_gr)
      | "ARRAY_SETL" ->
          let expl, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps -> If1.map_exp in_gr aexps [] do_simple_exp
                | Empty -> ([], in_gr))
          in
          let expl =
            List.map (fun x -> If1.find_incoming_regular_node x in_gr) expl
          in
          let in_ports = Array.make 2 "" in
          let out_ports = Array.make 1 "" in
          let (n, _, _), in_gr =
            If1.add_node_2 (`Simple (If1.ASETL, in_ports, out_ports, [])) in_gr
          in
          let array_triple, low_limit_triple =
            match expl with
            | [
             (array_node, array_port, array_type);
             (low_limit_node, low_limit_port, low_limit_type);
            ] ->
                ( (array_node, array_port, array_type),
                  (low_limit_node, low_limit_port, low_limit_type) )
            | _ ->
                failwith
                  ("Incorrect number of arguments for array_setl;"
                 ^ " Array_setl takes 2 arguments only")
          in
          let ( (array_node_id, array_port, array_type_id),
                (low_limit_node_id, low_limit_port, low_limit_type_id) ) =
            (array_triple, low_limit_triple)
          in
          let _ =
            match If1.lookup_ty array_type_id in_gr with
            | Array_ty _ -> ()
            | _ ->
                failwith
                  ("Incorrect type for array-setl; "
                 ^ "first argument must be an array, but found "
                  ^ If1.printable_full_type (If1.get_typemap_tm in_gr)
                      array_type_id)
          in
          let _ =
            match If1.lookup_ty low_limit_type_id in_gr with
            | Basic bx -> (
                match If1.is_basic_int_scalar bx with
                | false ->
                    failwith
                      ("Incorrect low limit type for array-setl; "
                     ^ "second argument must be an integer or long but found "
                      ^ If1.printable_full_type (If1.get_typemap_tm in_gr)
                          low_limit_type_id)
                | true -> ())
            | _ ->
                failwith
                  ("Incorrect low limit type for array-setl; "
                 ^ "second argument must be an integer or long but found "
                  ^ If1.printable_full_type (If1.get_typemap_tm in_gr)
                      low_limit_type_id)
          in
          let in_gr =
            If1.add_edge2 low_limit_node_id low_limit_port n 1 low_limit_type_id
              (If1.add_edge2 array_node_id array_port n 0 array_type_id in_gr)
          in
          ((n, 0, array_type_id), in_gr)
      | "ARRAY_FILL" ->
          let in_ports = Array.make 3 "" in
          let out_ports = Array.make 1 "" in

          let (n, _, _), in_gr =
            If1.add_node_2 (`Simple (If1.AFILL, in_ports, out_ports, [])) in_gr
          in

          let final_ty, in_gr =
            match arg with
            | Ast.Arg (Ast.Exp aexps) ->
                let arg_count, array_element_ty, in_gr =
                  List.fold_left
                    (fun (cou, element_ty, gr) x ->
                      let (l, m, tt), gr = do_simple_exp gr x in
                      let element_ty = if cou = 2 then tt else element_ty in
                      (cou + 1, element_ty, If1.add_edge l m n cou tt gr))
                    (0, 0, in_gr) aexps
                in

                if arg_count <> 3 then
                  raise (If1.Sem_error "ARRAY_FILL requires (low, high, value)");

                let (arr_ty_id, _, _), in_gr =
                  If1.add_type_to_typemap_dedup (If1.Array_ty array_element_ty)
                    in_gr
                in
                (arr_ty_id, in_gr)
            | _ -> raise (If1.Sem_error "Invalid arguments for ARRAY_FILL")
          in

          ((n, 0, final_ty), in_gr)
      | "ARRAY_SIZE" | "ARRAY_PREFIXSIZE" ->
          let in_port_00 = Array.make 1 "" in
          let out_port_00 = Array.make 1 "" in
          let (n, _, _), in_gr =
            If1.add_node_2
              (`Simple (If1.ASIZE, in_port_00, out_port_00, []))
              in_gr
          in
          let _, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps ->
                    List.fold_right
                      (fun x (cou, in_gr) ->
                        let (l, m, tt), in_gr = do_simple_exp in_gr x in
                        (cou + 1, If1.add_edge l m n cou tt in_gr))
                      aexps (0, in_gr)
                | _ -> (0, in_gr))
          in
          ((n, 0, If1.lookup_tyid INTEGRAL), in_gr)
      | "INNERPRODUCT" ->
          (* innerproduct(a, b) dispatches on types:
             vec * vec  → DOT       (scalar result)
             mat * mat  → MATMUL    (mat result)
             mat * vec  → MATVECMUL (vec result)
             vec * mat  → VECMATMUL (vec result) *)
          let args =
            match arg with
            | Ast.Arg (Ast.Exp exps) -> exps
            | _ -> raise (If1.Sem_error "innerproduct() requires two arguments")
          in
          if List.length args <> 2 then
            raise (If1.Sem_error "innerproduct() requires exactly two arguments");
          let (an, ap, at), in_gr = do_simple_exp in_gr (List.nth args 0) in
          let (bn, bp, bt), in_gr = do_simple_exp in_gr (List.nth args 1) in
          let a_ty = If1.lookup_ty at in_gr in
          let b_ty = If1.lookup_ty bt in_gr in
          let opcode, result_ty =
            match (If1.is_mat_type a_ty, If1.is_vector_type a_ty,
                   If1.is_mat_type b_ty, If1.is_vector_type b_ty) with
            | true, _, true, _ -> (If1.MATMUL,    at)
            | true, _, false, true -> (If1.MATVECMUL, bt)
            | false, true, true, _ -> (If1.VECMATMUL, at)
            | false, true, false, true ->
                let scalar_ty =
                  If1.find_ty in_gr (If1.get_element_type a_ty)
                in
                (If1.DOT, scalar_ty)
            | _ ->
                raise (If1.Sem_error
                  "innerproduct() requires mat or vec arguments")
          in
          let (rn, rp, _), in_gr =
            If1.add_node_2
              (`Simple (opcode, [| ""; "" |], [| "" |], [])) in_gr
          in
          let in_gr = If1.add_edge an ap rn 0 at in_gr in
          let in_gr = If1.add_edge bn bp rn 1 bt in_gr in
          ((rn, rp, result_ty), in_gr)
      | "STREAM_EMPTY" ->
          let (n, p, _), in_gr =
            If1.add_node_2
              (`Simple (If1.STRM_EMPTY, Array.make 1 "", Array.make 1 "", []))
              in_gr
          in
          let in_gr =
            match arg with
            | Ast.Arg (Ast.Exp [ expr ]) ->
                let (l, m, tt), in_gr = do_simple_exp in_gr expr in
                If1.add_edge l m n 0 tt in_gr
            | _ -> failwith "STREAM_EMPTY expects a single stream argument"
          in
          ((n, p, If1.lookup_tyid If1.BOOLEAN), in_gr)
      | ("STREAM_APPEND" | "STREAM_FIRST" | "STREAM_REST") as strm ->
          let in_port_00 = Array.make 1 "" in
          let out_port_00 = Array.make 1 "" in
          let node_name =
            match strm with
            | "STREAM_FIRST" -> If1.STRM_FIRST
            | "STREAM_REST" -> If1.STRM_REST
            | "STREAM_APPEND" -> If1.STRM_APPEND
            | _ -> failwith "Unknown function during stream processing"
          in
          let (n, _, _), in_gr =
            If1.add_node_2
              (`Simple (node_name, in_port_00, out_port_00, []))
              in_gr
          in
          let incoming_type, _, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps ->
                    List.fold_right
                      (fun x (prev, cou, in_gr) ->
                        let (l, m, tt), in_gr = do_simple_exp in_gr x in
                        let l, m, tt =
                          If1.find_incoming_regular_node (l, m, tt) in_gr
                        in
                        (tt :: prev, cou + 1, If1.add_edge l m n cou tt in_gr))
                      aexps ([], 0, in_gr)
                | _ -> ([], 0, in_gr))
          in
          let asty =
            if strm = "STREAM_FIRST" then
              match
                If1.TM.find_opt (List.hd incoming_type)
                  (If1.get_typemap_tm in_gr)
              with
              | None ->
                  failwith
                    ("Expected a stream data type for"
                   ^ " argument to stream_first")
              | Some (Stream bc) -> bc
              | Some xy ->
                  failwith
                    ("Expected a stream data type for"
                   ^ " argument to stream_first and found "
                    ^ If1.printable_full_type (If1.get_typemap_tm in_gr)
                        (List.hd incoming_type))
            else List.hd incoming_type
          in
          let _ =
            if strm = "STREAM_APPEND" then
              let _ = assert (List.length incoming_type == 2) in
              match incoming_type with
              | [ stream_ty; elem_ty ] ->
                  let stream_elem_ty =
                    match If1.lookup_ty stream_ty in_gr with
                    | If1.Stream e -> e
                    | _ -> stream_ty
                  in
                  if stream_elem_ty <> elem_ty then
                    failwith "Stream append element type does not match"
                  else ()
              | _ -> failwith "Syntax error in STREAM_APPEND"
            else ()
          in
          ((n, 0, asty), in_gr)
      | _ ->
          let expl, in_gr =
            match arg with
            | Ast.Arg aa -> (
                match aa with
                | Ast.Exp aexps -> If1.map_exp in_gr aexps [] do_simple_exp
                | Empty -> ([], in_gr))
          in
          let expl =
            List.map (fun x -> If1.find_incoming_regular_node x in_gr) expl
          in
          let arg_types = List.map (fun (_, _, t) -> t) expl in
          let cs, ps = in_gr.If1.symtab in
          let deref_fn =
            match String.uppercase_ascii deref_fn with _ -> deref_fn
          in
          let symtab_entry =
            match If1.SM.find_opt deref_fn cs with
            | Some id -> id
            | None -> (
                match If1.SM.find_opt deref_fn ps with
                | Some id -> id
                | None -> (
                    (* 2. Only mangle if exact name lookup fails *)
                    let target_prefix =
                      Printf.sprintf "_S%s__%s__" deref_fn
                        (String.concat ""
                           (List.map If1.short_name_for_intrinsic arg_types))
                    in
                    (* 3. Optimize prefix lookup *)
                    match If1.lookup_mangled_name target_prefix with
                    | Some id -> id
                    | None -> (
                        (* 4. Final Fallback: The "Discovery" scan *)
                        let discovered =
                          If1.lookup_partial_mangled_name target_prefix
                        in
                        match discovered with
                        | Some (_, id) -> id
                        | None ->
                            print_endline ("ARGUMENTS ARE " ^ Ast.str_arg arg);
                            flush stdout;
                            raise
                              (If1.Sem_error
                                 (If1.If1_View.export_debug_html "CRASHED_.html"
                                    in_gr;
                                  "Unknown function: " ^ deref_fn
                                  ^ " target prefix " ^ target_prefix)))))
          in
          let deref_fn = symtab_entry.val_name in
          let in_port_00 = Array.make (List.length expl) "" in
          let prags = [ If1.Name deref_fn ] in
          let (n, _, _), in_gr =
            If1.add_node_2
              (`Simple (If1.INVOCATION, in_port_00, out_port_0, prags))
              in_gr
          in
          let tm = If1.get_typemap_tm in_gr in
          let tml =
            match If1.TM.find_opt symtab_entry.val_ty tm with
            | Some x -> (
                match x with
                | If1.Function_ty (_, ret_ty, _) ->
                    let result = If1.fold_ret_ty_lis ret_ty tm in
                    result
                | _ ->
                    failwith
                      ("Expected function type but found: "
                     ^ If1.string_of_if1_ty x))
            | None -> (
                match If1.lookup_mangled_type symtab_entry.val_ty with
                | Some (If1.Function_ty (_, ret_ty, _)) ->
                    let _, intrinsic_types = Lazy.force If1.intrinsic_lib in
                    If1.fold_ret_ty_lis ret_ty intrinsic_types
                | _ -> failwith "Function type missing in typemap")
          in
          let _, output_triple_list =
            List.fold_right
              (fun ae (lev, re) -> (lev - 1, (n, lev, ae) :: re))
              tml
              (List.length tml - 1, [])
          in
          let in_gr = add_edges_in_list expl n 0 in_gr in
          if List.length output_triple_list = 1 then
            (List.hd output_triple_list, in_gr)
          else
            let (n1, _, _), in_gr =
              let in_port_01 = Array.make (List.length tml) "" in
              let out_port_01 = Array.make (List.length tml) "" in
              If1.add_node_2
                (`Simple (If1.MULTIARITY, in_port_01, out_port_01, prags))
                in_gr
            in
            let in_gr = add_edges_in_list output_triple_list n1 0 in_gr in
            ((n1, 0, 0), in_gr))
  | Array_ref (ar_a, ar_b) as aap ->
      let (arr_node, arr_port, att), in_gr = do_simple_exp in_gr ar_a in
      let (res_node, res_port, tt), in_gr_res =
        match ar_b with
        | Ast.Exp ex_lis ->
            let add_basic_arr_elem ((aaa, bbb, att), in_gr) arr_indx =
              let (idxnum, idxport, tt), in_gr = do_simple_exp in_gr arr_indx in
              let (arrnum, arrport, _), in_gr =
                If1.add_node_2
                  (`Simple (If1.AELEMENT, Array.make 2 "", Array.make 1 "", []))
                  in_gr
              in
              let in_gr = If1.add_edge idxnum idxport arrnum 1 tt in_gr in
              let in_gr = If1.add_edge aaa bbb arrnum 0 att in_gr in
              let inner_ty_num =
                match If1.lookup_ty att in_gr with
                | If1.Array_ty ij -> ij
                | _ ->
                    raise
                      (print_endline
                         (Ast.str_simple_exp aap ^ " Fails for "
                        ^ string_of_int att);
                       If1.If1_View.export_debug_html "compiler_failure.html"
                         in_gr;
                       If1.Sem_error
                         ("Situation:"
                         ^ If1.string_of_if1_ty (If1.lookup_ty att in_gr)))
              in
              ((arrnum, arrport, inner_ty_num), in_gr)
            in
            List.fold_left add_basic_arr_elem
              ((arr_node, arr_port, att), in_gr)
              ex_lis
        | _ -> ((arr_node, arr_port, att), in_gr)
      in
      ((res_node, res_port, tt), in_gr_res)
  | Let_rec (dp, e) ->
      (* 1. Setup Recursive Scope and Lower Inner Logic *)
      let let_gr = If1.inherit_parent_syms in_gr (If1.get_a_new_graph in_gr) in
      let _, let_gr = do_decldef_part_in_let_stmt (`Some 1) let_gr dp in
      let (frm, elp, elt), let_gr = do_exp let_gr e in
      let let_gr = point_edges_to_boundary frm elp elt let_gr in

      (* 2. Identify and Segregate Ports on Inner Boundary *)
      let port_type_map =
        If1.all_types_ending_at_no_err_ty 0 let_gr If1.IntMap.empty
      in
      let data_ports =
        If1.IntMap.filter
          (fun _ tid -> not (If1.is_error_port tid let_gr))
          port_type_map
      in
      let error_ports =
        If1.IntMap.filter
          (fun _ tid -> If1.is_error_port tid let_gr)
          port_type_map
      in

      (* 3. Add the Compound Node (add_node_2 will handle the 1-to-1 Propagator internally) *)
      let (aa, _, _), in_gr =
        If1.add_node_2
          (`Compound (let_gr, If1.INTERNAL, 0, [ If1.Name "LET_REC" ], []))
          in_gr
      in

      (* 4. PATH A: Scalarize Data Results *)
      let data_arity = If1.IntMap.cardinal data_ports in
      let (multinum, _, _), in_gr =
        build_multiarity ~nam:"LET_REC" data_arity in_gr
      in
      let in_gr =
        If1.IntMap.fold
          (fun port_idx tid acc_gr ->
            If1.add_edge aa port_idx multinum port_idx tid acc_gr)
          data_ports in_gr
      in
      (* 5. PATH B: Propagate Errors to Enclosing Boundary *)
      let in_gr =
        If1.IntMap.fold
          (fun port_idx tid acc_gr ->
            (* FIX: Use the getter instead of direct field access *)
            match If1.NM.find 0 (If1.get_node_map acc_gr) with
            | If1.Boundary (ins, outs, errs, prags) ->
                let next_b_port = List.length errs + 1 in
                (* Register error source in parent boundary metadata *)
                let updated_b =
                  If1.Boundary (ins, outs, errs @ [ (aa, tid) ], prags)
                in
                let acc_gr =
                  {
                    acc_gr with
                    If1.nmap = If1.NM.add 0 updated_b (If1.get_node_map acc_gr);
                  }
                in
                (* Physically wire Compound Error Port -> Parent Boundary Error Port *)
                If1.add_edge2 aa port_idx 0 next_b_port tid acc_gr
            | _ -> acc_gr)
          error_ports in_gr
      in
      ((multinum, 0, 0), in_gr)
  | Let (dp, in_exp) ->
      to_if1_msg 2 "Let: %s" (Ast.str_simple_exp (Let (dp, in_exp)));
      (* create a new graph with parent syms in ps and empty cs *)
      let let_gr = If1.inherit_parent_syms in_gr (If1.get_a_new_graph in_gr) in
      (* Give the dp argument to do_decldef_part_in_let_stmt *)
      let _, let_gr = do_decldef_part_in_let_stmt `None let_gr dp in
      (* lower the exp or the in component of a "let dp in exp"*)
      let (frm, elp, elt), let_gr = do_exp let_gr in_exp in
      (* connect the results from the expressions to the boundary *)
      (* When there is more than one output, the exp will
       * end with a MULTIARITY, and we need to connect each
       * incoming port to the multiarity to the boundary *)
      let let_gr = point_edges_to_boundary frm elp elt let_gr in
      (* 1. Identify all ports on the inner boundary *)
      let port_type_map =
        If1.all_types_ending_at_no_err_ty 0 let_gr If1.IntMap.empty
      in
      (* 2. Segregate Data vs Errors *)
      let data_ports =
        If1.IntMap.filter
          (fun _ tid -> not (If1.is_error_port tid let_gr))
          port_type_map
      in
      (* 3. Create the Compound Node *)
      (* Note: add_node_2 now internally calls
       * propagate_error_ports to lift inner errors
       * to the node's face *)
      let (aa, _, _), in_gr =
        If1.add_node_2
          (`Compound
             ( let_gr,
               If1.INTERNAL,
               0,
               [
                 If1.Name "LET_NON_REC";
                 If1.Ast_type (Ast.str_simple_exp (Let (dp, in_exp)));
               ],
               [] ))
          in_gr
      in
      (* 4. PATH A: Wire Data to MULTIARITY *)
      let data_arity = If1.IntMap.cardinal data_ports in
      let (multinum, _, _), in_gr =
        build_multiarity data_arity in_gr ~nam:"LET_NON_REC"
      in
      let _, in_gr =
        If1.IntMap.fold
          (fun port_idx tid (cur_num, acc_gr) ->
            (cur_num + 1, If1.add_edge aa port_idx multinum cur_num tid acc_gr))
          data_ports (0, in_gr)
      in
      ((multinum, 0, 0), in_gr)
  | Old (Ast.Value_name v) ->
      do_val_internal in_gr (`OldMob (String.concat "." v))
  | Val (Ast.Value_name v as m) -> do_val in_gr m
  | Paren e -> do_exp in_gr e
  (*| Tuple x -> (* Make a tuple type and insert it with a type*)*)
  | Array_generator_named tn ->
      let (bb, pp, _), in_gr =
        If1.add_node_2
          (`Simple (If1.ABUILD, Array.make 1 "", Array.make 1 "", []))
          in_gr
      in
      let tt = If1.lookup_by_typename in_gr tn in
      ((bb, pp, tt), in_gr)
  | Array_generator_named_addr (tn, ep) ->
      let tn = tn in
      array_builder_exp ~inc_typ:(If1.lookup_by_typename in_gr tn) in_gr ep
  | Array_generator_unnamed ep -> array_builder_exp in_gr ep
  | Array_replace (p, epl) ->
      let (sn, sp, arr_type), in_gr = do_simple_exp in_gr p in
      let rec do_array_replace ((sn, sp), in_gr) = function
        | Ast.SExpr_pair (idx, values) :: tl ->
            let (al, ap), in_gr =
              match values with
              | Empty -> failwith "Badly formed array replace"
              | Ast.Exp aexp ->
                  let bbu, in_gr = If1.map_exp in_gr aexp [] do_simple_exp in
                  let (idxnum, idxport, t2), in_gr = do_exp in_gr idx in
                  let (bb, pp, _), in_gr =
                    If1.add_node_2
                      (`Simple
                         ( If1.AREPLACE,
                           Array.make (List.length aexp + 2) "",
                           Array.make 1 "",
                           [] ))
                      in_gr
                  in
                  let in_gr =
                    If1.add_edge idxnum idxport bb 1 t2
                      (If1.add_edge sn sp bb 0 arr_type in_gr)
                  in
                  ((bb, pp), add_edges_in_list bbu bb 2 in_gr)
            in
            let (tan, tap), in_gr = do_array_replace ((al, ap), in_gr) tl in
            ((tan, tap), in_gr)
        | [] -> ((sn, sp), in_gr)
      in
      let (oa, oup), in_gr = do_array_replace ((sn, sp), in_gr) epl in
      ((oa, oup, arr_type), in_gr)
  | Ast.Record_ref (e, fn) ->
      to_if1_msg 2 "Record_ref: %s.%s" (Ast.str_simple_exp e)
        (Ast.str_field_name fn);
      let (ain, apo, tt1), in_gr = do_simple_exp in_gr e in
      let ain, apo, tt1 =
        If1.find_incoming_regular_node (ain, apo, tt1) in_gr
      in
      let input_type = If1.lookup_ty tt1 in_gr in
      if If1.is_vector_type input_type = true then (
        let fn = Ast.str_field_name fn in
        to_if1_msg 3 "Record_ref: vector swizzle %s on type %s" fn
          (If1.p_f_t in_gr tt1);
        let indices = crack_swizzle_mask (String.lowercase_ascii fn) in
        let (en, ep, input_ty), in_gr = ((ain, apo, tt1), in_gr) in
        let mask_len = List.length indices in

        (* 2. Replace the Literal Node with an ABUILD sequence *)
        (* This avoids the "122" string ambiguity *)
        let mask_ports, in_gr =
          List.fold_left
            (fun (acc, g) idx ->
              let (ln, lp, lt), g' =
                If1.add_node_2
                  (`Literal (If1.INTEGRAL, string_of_int idx, [| "" |]))
                  g
              in
              ((ln, lp, lt) :: acc, g'))
            ([], in_gr) indices
        in
        let mask_ports = List.rev mask_ports in

        (* 3. Create the ABUILD Node to hold the mask *)
        let (an, ap, at), in_gr =
          If1.add_node_2
            (`Simple (If1.ABUILD, Array.make mask_len "", Array.make 1 "", []))
            in_gr
        in

        (* 4. Wire Literal indices into ABUILD *)
        let in_gr =
          List.fold_left2
            (fun g i (ln, lp, lt) -> If1.add_edge ln lp an i lt g)
            in_gr
            (List.init mask_len (fun x -> x))
            mask_ports
        in

        (* 5. Determine Correct Return Type using your Weaver *)
        let st =
          let flavor = If1.get_element_type (If1.lookup_ty input_ty in_gr) in
          let res_struct =
            if mask_len = 1 then flavor
            else If1.build_vector_of_type flavor mask_len
          in
          If1.find_ty in_gr res_struct
        in

        (* 6. Create SWIZZLE Node (2 Inputs: 0=Vector, 1=Mask) *)
        let (sn, sp, _), in_gr =
          If1.add_node_2
            (`Simple (If1.SWIZZLE, [| ""; "" |], [| "" |], []))
            in_gr
        in

        (* 7. Final Wiring with corrected edge types *)
        ( (sn, sp, st),
          in_gr
          |> If1.add_edge an ap sn 1 at (* Mask goes to Port 1 *)
          |> If1.add_edge en ep sn 0
               input_ty (* Data goes to Port 0 (uses input_ty) *) ))
      else
        let fn = match fn with Ast.Field_name fn -> fn in
        to_if1_msg 3 "Record_ref: RELEMENTS field %s from type %s" fn
          (If1.p_f_t in_gr tt1);
        let _, tt2 = If1.get_record_field in_gr tt1 fn in
        let (bb, pp, _), in_gr =
          let in_porst = Array.make 2 "" in
          in_porst.(0) <- fn;
          If1.add_node_2
            (`Simple
               (If1.RELEMENTS, in_porst, Array.make 1 "", [ If1.No_pragma ]))
            in_gr
        in
        ((bb, pp, tt2), If1.add_edge ain apo bb 1 tt1 in_gr)
  | Ast.Record_array_ref (e, n) as re ->
      to_if1_msg 2 "Record_array_ref: %s splits as %s %s"
        (Ast.str_simple_exp re) (Ast.str_simple_exp e) (Ast.str_exp n);
      let (ain, apn, tt0), in_gr = do_simple_exp in_gr e in
      (* If the record field resolves to an array type, use AELEMENT subscripting
         (like Array_ref) to handle multi-index access like rec.field[i, j]. *)
      let is_array_ty =
        match If1.lookup_ty_safe tt0 in_gr with
        | Some (If1.Array_ty _) -> true
        | _ -> false
      in
      if is_array_ty then
        let add_basic_arr_elem ((aaa, bbb, att), in_gr) arr_indx =
          let (idxnum, idxport, tt), in_gr = do_simple_exp in_gr arr_indx in
          let (arrnum, arrport, _), in_gr =
            If1.add_node_2
              (`Simple (If1.AELEMENT, Array.make 2 "", Array.make 1 "", []))
              in_gr
          in
          let in_gr = If1.add_edge idxnum idxport arrnum 1 tt in_gr in
          let in_gr = If1.add_edge aaa bbb arrnum 0 att in_gr in
          let inner_ty_num =
            match If1.lookup_ty att in_gr with
            | If1.Array_ty ij -> ij
            | _ -> att
          in
          ((arrnum, arrport, inner_ty_num), in_gr)
        in
        let ex_lis = match n with Ast.Exp l -> l | _ -> [] in
        let (res_node, res_port, tt), in_gr_res =
          List.fold_left add_basic_arr_elem ((ain, apn, tt0), in_gr) ex_lis
        in
        ((res_node, res_port, tt), in_gr_res)
      else
        let (aim, apm, tt1), in_gr = do_exp in_gr n in
        let elem_ty =
          match If1.lookup_ty tt0 in_gr with
          | If1.Array_ty elem_id -> elem_id
          | _ -> tt0
        in
        to_if1_msg 3
          "Record_array_ref: array type %s, index type %s, elem type %s"
          (If1.p_f_t in_gr tt0) (If1.p_f_t in_gr tt1) (If1.p_f_t in_gr elem_ty);
        let (bb, pp, _), in_gr =
          let in_porst = Array.make 2 "" in
          in_porst.(0) <- Ast.str_simple_exp re;
          If1.add_node_2
            (`Simple
               (If1.RELEMENTS, in_porst, Array.make 2 "", [ If1.No_pragma ]))
            in_gr
        in
        ( (bb, pp, elem_ty),
          If1.add_edge ain apn bb 1 tt0 (If1.add_edge aim apm bb 0 tt1 in_gr) )
  | Ast.Record_generator_primary (e, fdle) ->
      let (e, p, inctt), in_gr = do_simple_exp in_gr e in
      let rec do_each_field ((a, b, tt), in_gr) = function
        | Ast.Field_exp (Ast.Field fi, se) :: tl ->
            let (aseb, asep, finaltt), in_gr = do_simple_exp in_gr se in
            let rec do_field_chain ((fe, ff, tt), in_gr) = function
              | Ast.Field_name fna :: tll ->
                  let (bb, bp, _), in_gr =
                    let in_porst = Array.make 3 "" in
                    in_porst.(1) <- fna;
                    let (bb, bp, _), in_gr =
                      If1.add_node_2
                        (`Simple
                           ( If1.RREPLACE,
                             in_porst,
                             Array.make 1 "",
                             [ If1.No_pragma ] ))
                        in_gr
                    in
                    ((bb, bp, tt), If1.add_edge fe ff bb 0 inctt in_gr)
                  in
                  let t1, _ = If1.get_record_field in_gr tt fna in
                  (* Below tt must be field name's id *)
                  do_field_chain ((bb, bp, t1), in_gr) tll
              | [] ->
                  ((fe, ff, finaltt), If1.add_edge aseb asep fe 2 finaltt in_gr)
            in
            do_each_field (do_field_chain ((a, b, tt), in_gr) fi) tl
        | [] -> ((a, b, inctt), in_gr)
      in
      do_each_field ((e, p, inctt), in_gr) fdle
  | Ast.Record_generator_unnamed fdl ->
      let (i, j, k), in_gr = record_builder in_gr fdl If1.Emp in
      ((i, j, k), in_gr)
  | Ast.Record_generator_named (tn, fdl) ->
      (* We can look up tn against known types.
        Following that we may have to thread in
        the If1.record type to the builder to
        check that the return types are correct. *)
      let xx = If1.lookup_by_typename in_gr tn in
      record_builder in_gr fdl (If1.Som xx)
  | Ast.Stream_generator tn ->
      let ty_id = If1.lookup_by_typename in_gr tn in
      let (n, p, _), in_gr =
        If1.add_node_2
          (`Simple
             (If1.SBUILD, Array.make 1 "", Array.make 1 "", [ If1.No_pragma ]))
          in_gr
      in
      ((n, p, ty_id), in_gr)
  | Ast.Stream_generator_exp (_, aexp) ->
      let myll, in_gr =
        match aexp with
        | Ast.Exp axep -> If1.map_exp in_gr axep [] do_simple_exp
        | _ -> ([], in_gr)
      in
      do_each_exp_in_strm in_gr myll
  | Ast.Stream_generator_unknown_exp aexp ->
      let myll, in_gr =
        match aexp with
        | Ast.Exp axep -> If1.map_exp in_gr axep [] do_simple_exp
        | _ -> ([], in_gr)
      in
      do_each_exp_in_strm in_gr myll
  | Ast.Union_generator (tn, te) ->
      (* Parameter port assignments are missing.
        Union's tag is missing in If1.RBUILD
        Are we supposed to use If1.RBUILD? *)
      let xx = If1.lookup_by_typename in_gr tn in
      union_builder in_gr te (If1.Som xx)
  | Ast.Tagcase (ae, tc, o) -> (
      to_if1_msg 2 "Tagcase: %s" (Ast.str_simple_exp (Ast.Tagcase (ae, tc, o)));
      (* Each tag is a graph, tagcase is a
       compound graph with one "input",
       which is the If1.union. So while creating
       a graph for a tag, we have to provide
       the tag's type as the incoming type in its
       boundary--- will need to get a symbol name from
       tagcase_exp and an If1.union type from the RHS to
       add the vn_n as a If1.symtab entry of type tyy.
       Finally, will need to add the above symbol name to the
       boundaries of a new graph and set the type from the
       tag name. *)
      let (_, _, aunion_type), in_gr, vn_n =
        match ae with
        | Assign (vn, e) ->
            let vn_n =
              match vn with Ast.Value_name vnn -> String.concat "." vnn
            in
            let (an, po, tyy), in_gr = do_simple_exp in_gr e in
            ((an, po, tyy), in_gr, vn_n)
        | Tagcase_exp e ->
            let (an, po, tyy), in_gr = do_simple_exp in_gr e in
            ((an, po, tyy), in_gr, "__tagcase_expr__")
      in
      (* Walk over If1.typemap lists and collect
        the union's tag#s *)
      let tag_nums = enumerate_union_tags aunion_type in_gr in
      (* The tags follow the If1.union type in
        the above list, but
        the list needs reversing first. *)
      let tag_nums = List.tl (List.rev tag_nums) in
      (* get one subgraph for each tag in the variant
        cases, except for otherwise, which follows
        down below. The function that generates the
        subgraphs is tag_builder. It adds the subgraphs
        to the newly setup graph: tagcase_gr_.*)
      let output_type_list, tagcase_gr_, tag_map =
        let tagcase_gr_ = new_graph_for_tag_case vn_n aunion_type in_gr in
        tag_builder aunion_type in_gr tagcase_gr_ tc vn_n If1.IntMap.empty
          If1.IntMap.empty
      in
      match o with
      | Otherwise e ->
          let gr_o =
            match e with
            | Ast.Empty -> tagcase_gr_
            | _ ->
                let outlis, _, gr_o =
                  get_new_tagcase_graph tagcase_gr_ `OtherwiseTag e
                in
                let jj, gr_o = extr_types gr_o (outlis, If1.IntMap.empty) in
                let _ = check_tag_types vn_n jj output_type_list tagcase_gr_ in
                tagcase_gr_
          in
          let (aa, _, _), tagcase_gr =
            If1.add_node_2
              (`Compound (gr_o, If1.INTERNAL, 0, [ If1.Name "OTHERWISE" ], []))
              tagcase_gr_
          in
          (* Build assoc_list: tag_builder would have
           a key-value for the listed variants
           and remaining would be
           using the Otherwise subgraph.*)
          let assoc_lis =
            List.fold_right
              (fun x outl ->
                match If1.IntMap.mem x tag_map with
                | true -> If1.IntMap.find x tag_map :: outl
                | false -> aa :: outl)
              tag_nums []
          in
          let (fin_node, fin_por, fin_tyy), out_gr =
            If1.add_node_2
              (`Compound
                 ( tagcase_gr,
                   If1.TAGCASE,
                   0,
                   [ If1.Name "If1.TAGCASE" ],
                   assoc_lis ))
              in_gr
          in

          to_if1_msg 4 "tagcase: before add_edges_to_boundary fin_node=%d"
            fin_node;
          let tagcase_g = add_edges_to_boundary tagcase_gr out_gr fin_node in
          if If1.IntMap.is_empty output_type_list then
            ((fin_node, fin_por, fin_tyy), tagcase_g)
          else
            add_edges_from_inner_to_outer output_type_list tagcase_g fin_node
              "TAGCASE")
  | Is (tag_nam, e) ->
      (* In addition to the true and false literals
        that are returned by Is, we may also need to
        return an error ty. This might be for cases
        when the expected tag does not match with
        any of the tags of the If1.union ty- we will have
        to do this later on. *)
      let tm = If1.get_typemap_tm in_gr in
      let tn_ty =
        match find_matching_union_str tag_nam tm with
        | If1.Emp -> failwith "UNKNOWN TAG IN AN UNION"
        | If1.Som k -> k
      in
      let (un_num, un_po, un_ty), in_gr = do_exp in_gr e in
      let un_num, un_po, un_ty =
        If1.find_incoming_regular_node (un_num, un_po, un_ty) in_gr
      in
      let tag_nums = enumerate_union_tags un_ty in_gr in
      let tag_nums = List.map (fun c -> if c = tn_ty then 1 else 0) tag_nums in
      let test_graph = If1.get_a_new_graph in_gr in
      let false_lit, test_graph =
        If1.add_node_2 (`Literal (If1.BOOLEAN, "False", out_port_1)) test_graph
      in
      let true_lit, test_graph =
        If1.add_node_2 (`Literal (If1.BOOLEAN, "True", out_port_1)) test_graph
      in
      let test_graph =
        If1.output_to_boundary [ false_lit; true_lit ] test_graph
      in
      let (co_num, co_po, _), in_gr =
        If1.add_node_2
          (`Compound
             ( test_graph,
               If1.INTERNAL,
               0,
               [ If1.Name ("IS_SUBGRAPH" ^ string_of_int un_ty) ],
               tag_nums ))
          in_gr
      in
      let in_gr = If1.add_edge un_num un_po co_num co_po un_ty in_gr in
      ((co_num, co_po, If1.lookup_tyid If1.BOOLEAN), in_gr)
  | Prefix_operation (pn, e) ->
      let (typecast_arg_node, typecast_arg_out_port, typecast_arg_type), in_gr =
        do_exp in_gr e
      in
      let typecast_out_type = If1.lookup_tyid (If1.get_typecast_type pn) in
      let (typecast_node, typecast_out_port, _), in_gr =
        If1.add_node_2
          (`Simple
             (If1.TYPECAST, Array.make 1 "", Array.make 1 "", [ If1.No_pragma ]))
          in_gr
      in
      ( (typecast_node, typecast_out_port, typecast_out_type),
        in_gr
        |> If1.add_edge typecast_arg_node typecast_arg_out_port typecast_node 0
             typecast_arg_type )
  | Is_error e ->
      let (n, p, t), in_gr = do_exp in_gr e in
      let n, p, t = first_incoming_triple_to_multiarity n in_gr in
      let node_config =
        `Simple
          ( If1.ERROR_NODE,
            Array.make 1 "",
            (* Input ports: fields + optional base *)
            Array.make 1 "",
            (* Output ports *)
            [ If1.No_pragma ] )
      in
      let (node_id, port_id, _), in_gr = If1.add_node_2 node_config in_gr in
      let in_gr = If1.add_edge2 n p node_id 0 t in_gr in
      ((node_id, port_id, If1.lookup_tyid If1.BOOLEAN), in_gr)
  | If (cl, Else el) as if_ast ->
      to_if1_msg 2 "If: %s" (Ast.str_simple_exp if_ast);
      (* if_builder cl in_gr_if els
         Builds all subgraphs (PREDICATE, BODY, ELSE compounds) and SELECT nodes
         inside in_gr_if.  On return, in_gr_if's boundary exports the N final
         selected result values at consecutive ports 0..N-1.
         Returns (ty_lis, in_gr_if) where ty_lis has N type entries. *)
      (* Helper: after creating a compound node from a subgraph with N data outputs,
         reconstruct a MULTIARITY in the outer graph with edges coming in from the
         compound's output ports (which mirror the subgraph's boundary outputs).
         Returns (compound_n, multiarity_n, updated_outer_gr). *)
      let build_compound_and_ma sub_gr ty_lis pragmas outer_gr =
        let (cn, _, _), outer_gr =
          If1.add_node_2 (`Compound (sub_gr, If1.INTERNAL, 0, pragmas, [])) outer_gr
        in
        let n = If1.IntMap.cardinal ty_lis in
        let (ma_n, _, _), outer_gr = build_multiarity n outer_gr ~nam:"BRANCH_MA" in
        let outer_gr, _ =
          If1.IntMap.fold
            (fun _ result_ty (gr, k) ->
              (If1.add_edge cn k ma_n k result_ty gr, k + 1))
            ty_lis (outer_gr, 0)
        in
        (cn, ma_n, outer_gr)
      in
      let rec if_builder cl in_gr_if els =
        match cl with
        | Ast.Cond (predicate, body) :: tl ->
            to_if1_msg 3 "If: lowering ELSE chain: %s" (Ast.str_exp predicate);
            (* 1. Build else chain in its own subgraph; unravel to boundary,
               then reconstruct MULTIARITY in in_gr_if from compound outputs. *)
            let ty_lis_else, else_gr =
              let grr_th = If1.get_a_new_graph in_gr_if in
              if_builder tl grr_th els
            in
            let else_cn, else_ma, in_gr_if =
              build_compound_and_ma else_gr ty_lis_else
                [ If1.Name "ELSE"; If1.Ast_type (Ast.str_exp els) ]
                in_gr_if
            in
            let in_gr_if = add_edges_to_boundary else_gr in_gr_if else_cn in

            (* 2. Build then body; unravel to boundary, reconstruct MULTIARITY. *)
            to_if1_msg 3 "If: lowering BODY: %s" (Ast.str_exp body);
            let in_outs, then_gr = do_exp (If1.get_a_new_graph in_gr_if) body in
            let ty_lis_then, then_gr =
              extr_types then_gr (in_outs, If1.IntMap.empty)
            in
            let then_s, then_p, then_t = in_outs in
            let then_gr =
              point_edges_to_boundary then_s then_p then_t then_gr
            in
            let then_cn, then_ma, in_gr_if =
              build_compound_and_ma then_gr ty_lis_then
                [ If1.Name "BODY"; If1.Ast_type (Ast.str_exp body) ]
                in_gr_if
            in
            let in_gr_if = add_edges_to_boundary then_gr in_gr_if then_cn in

            (* 3. Check arity *)
            let fmt_ty_map m =
              let tm = If1.get_typemap_tm in_gr_if in
              let bindings =
                If1.IntMap.bindings (filter_data_types in_gr_if m)
              in
              "["
              ^ String.concat "; "
                  (List.map
                     (fun (port, tid) ->
                       Printf.sprintf "p%d:%s" port
                         (If1.printable_full_type tm tid))
                     bindings)
              ^ "]"
            in
            to_if1_msg 3 "If: check subgraph tys: then=%s else=%s"
              (fmt_ty_map ty_lis_then) (fmt_ty_map ty_lis_else);
            let _ =
              check_subgr_tys in_gr_if
                (Ast.str_cond (Ast.Cond (predicate, body)))
                ty_lis_then ty_lis_else
            in

            (* 4. Build predicate *)
            to_if1_msg 3 "If: lowering PREDICATE: %s" (Ast.str_exp predicate);
            let pred_out, predicate_gr =
              do_exp (If1.get_a_new_graph in_gr_if) predicate
            in
            let _, predicate_gr =
              extr_types predicate_gr (pred_out, If1.IntMap.empty)
            in
            let pred_s, pred_p, pred_t = pred_out in
            let predicate_gr =
              point_edges_to_boundary pred_s pred_p pred_t predicate_gr
            in
            let (pn, _, _), in_gr_if =
              If1.add_node_2
                (`Compound
                   ( predicate_gr,
                     If1.INTERNAL,
                     0,
                     [
                       If1.Name "PREDICATE";
                       If1.Ast_type (Ast.str_exp predicate);
                     ],
                     [] ))
                in_gr_if
            in
            let in_gr_if = add_edges_to_boundary predicate_gr in_gr_if pn in

            (* 5. Create one SELECT node per output value.
               SELECT_k: input 0 = pred bool, input 1 = then_ma:k, input 2 = else_ma:k.
               then_ma/else_ma are MULTIARITYs whose k-th input comes from the
               respective branch compound's k-th output. *)
            let in_gr_if, sel_results =
              If1.IntMap.fold
                (fun _ result_ty (gr, (k, results)) ->
                  let (sel_n, _, _), gr =
                    If1.add_node_2
                      (`Simple
                         ( If1.SELECT,
                           Array.make 3 "",
                           Array.make 1 "",
                           [ If1.Name (Printf.sprintf "SELECT_%d" k) ] ))
                      gr
                  in
                  let gr = If1.add_edge pn 0 sel_n 0 pred_t gr in
                  let gr = If1.add_edge then_ma k sel_n 1 result_ty gr in
                  let gr = If1.add_edge else_ma k sel_n 2 result_ty gr in
                  (gr, (k + 1, results @ [ (sel_n, result_ty) ])))
                ty_lis_then (in_gr_if, (0, []))
            in
            let _, sel_results = sel_results in

            (* 6. Collect SELECT outputs into a MULTIARITY, then unravel it to
               this graph's boundary — mirrors the pattern used for THEN/ELSE. *)
            let n_sel = List.length sel_results in
            let (sel_ma, _, _), in_gr_if =
              build_multiarity n_sel in_gr_if ~nam:"SEL_MA"
            in
            let in_gr_if, _ =
              List.fold_left
                (fun (gr, k) (sel_n, result_ty) ->
                  (If1.add_edge sel_n 0 sel_ma k result_ty gr, k + 1))
                (in_gr_if, 0) sel_results
            in
            let first_sel_ty = snd (List.hd sel_results) in
            let in_gr_if =
              point_edges_to_boundary sel_ma 0 first_sel_ty in_gr_if
            in
            (ty_lis_then, in_gr_if)
        | [] ->
            (* Final else: evaluate, wire to boundary, return types *)
            to_if1_msg 3 "If: lowering final ELSE: %s" (Ast.str_exp els);
            let (else_s, else_p, else_t), i_gr = do_exp in_gr_if els in
            let ty_lis, i_gr =
              extr_types i_gr ((else_s, else_p, else_t), If1.IntMap.empty)
            in
            let i_gr = point_edges_to_boundary else_s else_p else_t i_gr in
            (* i_gr boundary now has N outputs at consecutive ports 0..N-1 *)
            (ty_lis, i_gr)
      in
      let sai, gai =
        let ty_lis, regar =
          let regar = If1.get_a_new_graph in_gr in
          if_builder cl regar el
        in
        (* regar's boundary has N outputs = SELECT results.
           Create the outer compound, then always reconstruct a MULTIARITY
           collecting its outputs so callers get a uniform MULTIARITY handle. *)
        let name_it =
          If1.IntMap.fold
            (fun _ ed_ty out_str ->
              If1.printable_full_type (If1.get_typemap_tm in_gr) ed_ty
              ^ "; " ^ out_str)
            ty_lis ""
        in
        let (sn, _, _), in_gr =
          If1.add_node_2
            (`Compound
               ( regar,
                 If1.INTERNAL,
                 0,
                 [
                   If1.Name ("IF_" ^ name_it);
                   If1.Ast_type (Ast.str_simple_exp if_ast);
                 ],
                 [] ))
            in_gr
        in
        (* Always reconstruct MULTIARITY from sn:0..N-1 (even for N=1) so
           callers receive all N values through the standard mechanism. *)
        let n = If1.IntMap.cardinal ty_lis in
        let (ma_n, _, _), in_gr =
          build_multiarity n in_gr ~nam:"IF_RESULT"
        in
        let in_gr, _ =
          If1.IntMap.fold
            (fun _ result_ty (gr, k) ->
              (If1.add_edge sn k ma_n k result_ty gr, k + 1))
            ty_lis (in_gr, 0)
        in
        let _, first_ty = If1.IntMap.min_binding ty_lis in
        ((ma_n, 0, first_ty), in_gr)
      in
      (sai, gai)
  | For_all (i, d, r) ->
      to_if1_msg 2 "For_all: %s" (Ast.str_simple_exp (For_all (i, d, r)));
      (* First we build a hierarchy based on in-exps,
        then we add the body/returns in it. Perhaps
        we could do this easily... i am not sure yet *)
      let (fx, fy, fz), _, in_gr = do_for_all i d r in_gr in
      (* TODO: Need To Check Vs If1, Add Assoc List *)
      (* How Do We Tie Up Results To Calling Function
        Or To A Let Var *)
      ((fx, fy, fz), in_gr)
  | For_initial (d, i, r) as finit ->
      to_if1_msg 2 "For_initial: %s" (Ast.str_simple_exp finit);
      let add_decls in_gr dp =
        to_if1_msg 3 "For_initial: lowering INIT";
        let build_init_graph in_gr =
          let init_gr =
            get_ports_unified (If1.get_a_new_graph in_gr) in_gr in_gr
          in
          init_gr
        in
        let xyz, out_gr = do_decldef_part (build_init_graph in_gr) dp in
        let _, out_gr =
          let cs = fst out_gr.If1.symtab in
          If1.SM.fold
            (fun _
                 {
                   If1.val_name = _;
                   If1.val_ty = t1;
                   If1.val_def = dd;
                   If1.def_port = dp;
                 } (op, out_gr) ->
              if dd <> 0 then (op + 1, If1.add_edge dd dp 0 op t1 out_gr)
              else (op, out_gr))
            cs
            (If1.boundary_in_port_count out_gr, out_gr)
        in
        (xyz, out_gr)
      in

      let add_terminator init_gr t =
        to_if1_msg 3 "For_initial: lowering TEST";
        let build_term_graph init_gr =
          let term_gr =
            get_ports_unified (If1.get_a_new_graph init_gr) init_gr init_gr
          in
          If1.inherit_parent_syms init_gr term_gr
        in
        let (tn, tp, tt), init_gr =
          do_termination (build_term_graph init_gr) t
        in
        ((tn, tp, tt), If1.output_to_boundary [ (tn, tp, tt) ] init_gr)
      in

      let add_body init_gr bi rclau =
        to_if1_msg 3 "For_initial: lowering BODY";
        let build_body_graph init_gr =
          let body_gr =
            get_ports_unified (If1.get_a_new_graph init_gr) init_gr init_gr
          in
          If1.inherit_parent_syms init_gr body_gr
        in
        let bbr = build_body_graph init_gr in
        let (_, _, _), body_gr = do_iterator bbr bi in
        let body_gr, return_action_list, ret_tuple_list, mask_ty_list =
          do_returns_clause_list body_gr rclau [] [] []
        in
        If1.If1_View.export_debug_html "BEFORE.html" body_gr;
        let body_gr =
          If1.output_bound_names_for_subgraphs ret_tuple_list body_gr
        in
        If1.If1_View.export_debug_html "AFTER.html" body_gr;
        (body_gr, return_action_list, ret_tuple_list, mask_ty_list)
      in

      let add_comp_node in_gr namen ?(prag = "") to_gr =
        let prags =
          if prag <> "" then If1.Name namen :: [ If1.Ast_type prag ]
          else [ If1.Name namen ]
        in
        let _, on =
          If1.add_node_2 (`Compound (in_gr, If1.INTERNAL, 0, prags, [])) to_gr
        in
        on
      in

      let loopAOrB i in_gr =
        match i with
        | Ast.Iterator_termination (ii, t) ->
            to_if1_msg 3 "LoopA: building INIT decls";
            let (_, _, _), decl_gr = add_decls in_gr d in
            (* Build BODY before TEST: the repeat body may declare variables
               (e.g. x_error) that are referenced in the until/while condition. *)
            to_if1_msg 3 "LoopA: building BODY iterator: %s"
              (Ast.str_iterator ii);
            let body_gr, return_action_list, _, mask_ty_list =
              add_body decl_gr ii r
            in
            to_if1_msg 3 "LoopA: building TEST termination: %s"
              (Ast.str_termination t);
            let (_, _, _), test_gr = add_terminator body_gr t in
            to_if1_msg 3 "LoopA: building RETURNS (%d clauses)"
              (List.length return_action_list);
            let (_, _, _), for_gr, return_action_list =
              add_ret body_gr return_action_list mask_ty_list
                (String.concat "\n" (List.map Ast.str_return_clause r))
            in
            let for_gr =
              add_comp_node body_gr "BODY"
                ~prag:
                  (Ast.str_decldef_part (`Loop_type d)
                  ^ "\n" ^ Ast.str_iterator ii ^ "\n" ^ Ast.str_termination t)
                for_gr
            in
            let for_gr =
              add_comp_node test_gr "TEST"
                ~prag:(Ast.str_iterator ii ^ "\n" ^ Ast.str_termination t)
                for_gr
            in
            let for_gr =
              add_comp_node decl_gr "INIT"
                ~prag:(Ast.str_decldef_part (`Loop_type d))
                for_gr
            in
            let for_gr = get_ports_unified for_gr body_gr decl_gr in
            let (fx, _, _), in_gr =
              If1.add_node_2
                (`Compound
                   ( for_gr,
                     If1.INTERNAL,
                     0,
                     [
                       If1.Name "LoopA"; If1.Ast_type (Ast.str_simple_exp finit);
                     ],
                     let lis = get_assoc_list_loopAOrB for_gr in
                     List.length lis :: lis ))
                in_gr
            in
            to_if1_msg 3
              "LoopA: outer compound node=%d, building multiarity for %d \
               return(s)"
              fx
              (List.length return_action_list);
            let (mul_n, mul_p, mul_t), in_gr =
              build_multiarity
                (List.length return_action_list)
                in_gr ~nam:"FOR_INITIAL_LOOP_A"
            in
            let _, _, in_gr =
              List.fold_right
                (fun (wh, tt, aa) (cc, outl, iigr) ->
                  to_if1_msg 4 "LoopA: wiring fx:%d -> mul_n:%d ty=%s" aa cc
                    (If1.p_f_t iigr tt);
                  ( cc + 1,
                    (wh, tt, fx, cc) :: outl,
                    If1.add_edge2 fx aa mul_n cc tt iigr ))
                return_action_list (0, [], in_gr)
            in
            to_if1_msg 3 "LoopA: tying outer scope to inner, multiarity node=%d"
              mul_n;
            let in_gr = tie_outer_scope_to_inner for_gr in_gr fx in
            ((mul_n, mul_p, mul_t), in_gr)
        | Termination_iterator (t, ii) ->
            to_if1_msg 3 "LoopB: building INIT decls";
            let (_, _, _), decl_gr = add_decls in_gr d in
            to_if1_msg 3 "LoopB: building TEST termination: %s"
              (Ast.str_termination t);
            let (_, _, _), test_gr = add_terminator decl_gr t in
            to_if1_msg 3 "LoopB: building BODY iterator: %s"
              (Ast.str_iterator ii);
            let body_gr, return_action_list, _, mask_ty_list =
              add_body test_gr ii r
            in
            to_if1_msg 3 "LoopB: building RETURNS (%d clauses)"
              (List.length return_action_list);
            let (_, _, _), for_gr, return_action_list =
              add_ret body_gr return_action_list mask_ty_list
                (String.concat "\n" (List.map Ast.str_return_clause r))
            in
            let for_gr =
              add_comp_node body_gr "BODY"
                ~prag:
                  (Ast.str_decldef_part (`Loop_type d)
                  ^ "\n" ^ Ast.str_termination t ^ "\n" ^ Ast.str_iterator ii)
                for_gr
            in
            let for_gr =
              add_comp_node test_gr "TEST"
                ~prag:(Ast.str_termination t ^ "\n" ^ Ast.str_iterator ii)
                for_gr
            in
            let for_gr =
              add_comp_node decl_gr "INIT"
                ~prag:(Ast.str_decldef_part (`Loop_type d))
                for_gr
            in
            let for_gr = get_ports_unified for_gr body_gr in_gr in
            let (fx, _, _), in_gr =
              If1.add_node_2
                (`Compound
                   ( for_gr,
                     If1.INTERNAL,
                     0,
                     [
                       If1.Name "LoopB"; If1.Ast_type (Ast.str_simple_exp finit);
                     ],
                     let lis = get_assoc_list_loopAOrB for_gr in
                     List.length lis :: lis ))
                in_gr
            in

            to_if1_msg 3
              "LoopB: outer compound node=%d, building multiarity for %d \
               return(s)"
              fx
              (List.length return_action_list);
            let (mul_n, mul_p, mul_t), in_gr =
              build_multiarity
                (List.length return_action_list)
                in_gr ~nam:"FOR_INITIAL_LOOP_B"
            in
            let _, _, in_gr =
              List.fold_right
                (fun (wh, tt, aa) (cc, outl, iigr) ->
                  to_if1_msg 4 "LoopB: wiring return port %d ty=%s" cc
                    (If1.p_f_t iigr tt);
                  ( cc + 1,
                    (wh, tt, fx, cc) :: outl,
                    If1.add_edge2 fx aa mul_n cc tt iigr ))
                return_action_list (0, [], in_gr)
            in
            to_if1_msg 3 "LoopB: tying outer scope to inner, multiarity node=%d"
              mul_n;
            let in_gr = tie_outer_scope_to_inner for_gr in_gr fx in
            ((mul_n, mul_p, mul_t), in_gr)
      in
      loopAOrB i in_gr
  | Tuple e ->
      (* #(expr) - tuple expression: lower the inner exp and mark the
         resulting MULTIARITY (if any) as a TUPLE_VAL so downstream code
         can distinguish it from a plain multi-value function return. *)
      let (frm, elp, elt), in_gr = do_exp in_gr e in
      let in_gr =
        match If1.get_node frm in_gr with
        | If1.Simple (lab, If1.MULTIARITY, pin, pout, _) ->
            let node =
              If1.Simple (lab, If1.MULTIARITY, pin, pout, [ If1.Name "TUPLE_VAL" ])
            in
            { in_gr with If1.nmap = If1.NM.add frm node in_gr.If1.nmap }
        | _ -> in_gr
      in
      ((frm, elp, elt), in_gr)

and find_in_graph_from_pragma in_gr namen =
  let tail = in_gr.If1.w in
  let nm = in_gr.If1.nmap in
  let rec gen_gr tl =
    if tl = tail then `Nth
    else
      let agr =
        try If1.NM.find tl nm
        with _ ->
          failwith
            (print_endline (String.concat "." (If1.string_of_node_map in_gr));
             "Fail here in find_in_graph_from_pragma " ^ string_of_int tl)
      in
      match agr with
      | Compound (lab, sy, _, pl, g, assoc) ->
          if
            (try List.hd pl
             with _ -> raise (If1.Sem_error "Error lowering for pragma"))
            = If1.Name namen
          then `Found_one (lab, sy, pl, g, assoc)
          else gen_gr (tl + 1)
      | _ -> gen_gr (tl + 1)
  in
  gen_gr 0

and do_return_exp in_gr ggg =
  match ggg with
  | Ast.Value_of (reduc_dir, reduc_name, expn) ->
      let reduc_dir =
        match reduc_dir with
        | Ast.No_dir -> `JustReduce
        | Ast.Left -> `RedLeft
        | Ast.Right -> `RedRight
        | Ast.Tree -> `RedTree
      in
      let reduc_name =
        match reduc_name with
        | Ast.Sum -> "sum"
        | Ast.Product -> "product"
        | Ast.Least -> "least"
        | Ast.Greatest -> "greatest"
        | Ast.Catenate -> "catenate"
        | Ast.No_red -> "NoRed"
      in
      let (val_of, val_po, val_ty), in_gr = do_simple_exp in_gr expn in
      let val_of, val_po, val_ty =
        If1.find_incoming_regular_node (val_of, val_po, val_ty) in_gr
      in
      if String.equal reduc_name "NoRed" then
        (`FinalVal, (val_of, val_po, val_ty), in_gr)
      else (`Reduce (reduc_dir, reduc_name), (val_of, val_po, val_ty), in_gr)
  | Ast.Array_of e ->
      let (an, ap, at), in_gr = do_simple_exp in_gr e in
      let an, ap, at = If1.find_incoming_regular_node (an, ap, at) in_gr in
      assert (at <> 0);
      (`Array_of, (an, ap, at), in_gr)
  | Ast.Stream_of e ->
      let (sn, sp, st), in_gr = do_simple_exp in_gr e in
      let sn, sp, st = If1.find_incoming_regular_node (sn, sp, st) in_gr in
      assert (st <> 0);
      (`Stream_of, (sn, sp, st), in_gr)

and add_return_gr in_gr body_gr return_action_list mask_ty_list prag =
  let ret_gr =
    try If1.create_subgraph_symtab in_gr (If1.get_a_new_graph body_gr)
    with _ -> failwith "create subgraph symtab"
  in
  let ret_gr = get_ports_unified ret_gr in_gr in_gr in
  (* NEED TO ADD STREAM RETURN *)
  let do_reduc ((rdx, red_fn), tt, aa) msk_opt in_gr =
    let out_port_1 =
      let out_array = Array.make 1 "" in
      out_array
    in
    let which_ins =
      match rdx with
      | `JustReduce -> If1.REDUCE
      | `RedLeft -> If1.REDUCELEFT
      | `RedRight -> If1.REDUCERIGHT
      | `RedTree -> If1.REDUCETREE
    in
    let (dd, ee, _), in_gr =
      If1.add_node_2
        (`Simple (which_ins, Array.make 3 "", Array.make 1 "", [ If1.No_pragma ]))
        in_gr
    in
    let (lx, ly, _), in_gr =
      If1.add_node_2 (`Literal (If1.CHARACTER, red_fn, out_port_1)) in_gr
    in
    let in_gr = If1.add_edge lx ly dd 0 (If1.lookup_tyid If1.CHARACTER) in_gr in
    let in_gr = If1.add_edge 0 aa dd 1 tt in_gr in
    (* NEW: Port 2: Conditional Mask (if present) *)
    let in_gr =
      match msk_opt with
      | Some (mask_ty, mask_port) -> If1.add_edge 0 mask_port dd 2 mask_ty in_gr
      | None -> in_gr
    in
    If1.add_to_boundary_outputs dd ee tt in_gr
  in
  let ret_gr, _, _, out_lis =
    let rec create_return_nodes out_gr in_count out_count out_lis
        return_action_list mask_ty_list =
      match (return_action_list, mask_ty_list) with
      | [], [] -> (out_gr, in_count, out_count, out_lis)
      | hd_a :: tl_return_action_list, hd_c :: tl_mask_ty_list -> (
          match hd_a with
          | `Array_of, tt, aa ->
              assert (tt <> 0);
              let (dd, ee, _), out_gr =
                If1.add_node_2
                  (`Simple
                     ( If1.AGATHER,
                       Array.make 2 "",
                       Array.make 1 "",
                       [ If1.No_pragma ] ))
                  out_gr
              in
              (* Create a type for AGATHER HERE AND ADD ITS TYPE TO
              output return_action_list *)
              let what_ty, out_gr =
                assert (tt <> 0);
                let (id_x, _, _), out_gr =
                  If1.add_type_to_typemap_dedup (If1.Array_ty tt) out_gr
                in
                (id_x, out_gr)
              in
              let out_gr =
                If1.add_edge 0 0 dd 0 5 (*integer type for indx*) out_gr
              in
              let out_gr = If1.add_edge 0 aa dd 1 tt out_gr in
              let out_gr = If1.add_to_boundary_outputs dd ee what_ty out_gr in
              let out_gr =
                match hd_c with
                | Some (aty, pnum) -> If1.add_edge 0 pnum dd 2 aty out_gr
                | None -> out_gr
              in
              create_return_nodes out_gr (in_count + 2) (out_count + 1)
                (out_lis @ [ (`Array_of, what_ty, out_count) ])
                tl_return_action_list tl_mask_ty_list
          | `FinalVal, tt, aa ->
              to_if1_msg 4
                "create_return_nodes: FinalVal in_port=%d out_port=%d ty=%s" aa
                out_count (If1.p_f_t out_gr tt);
              let out_gr =
                let (dd, ee, _), out_gr =
                  If1.add_node_2
                    (`Simple
                       ( If1.FINALVALUE,
                         Array.make 2 "",
                         Array.make 1 "",
                         [ If1.No_pragma ] ))
                    out_gr
                in
                let out_gr = If1.add_edge 0 aa dd 0 tt out_gr in
                If1.add_to_boundary_outputs dd ee tt out_gr
              in
              create_return_nodes out_gr (in_count + 1) (out_count + 1)
                (out_lis @ [ (`FinalVal, tt, out_count) ])
                tl_return_action_list tl_mask_ty_list
          | `Reduce (`JustReduce, red_fn), tt, aa ->
              let out_gr =
                do_reduc ((`JustReduce, red_fn), tt, aa) hd_c in_gr
              in
              create_return_nodes out_gr (in_count + 1) (out_count + 1)
                (out_lis @ [ (`Reduce (`JustReduce, red_fn), tt, out_count) ])
                tl_return_action_list tl_mask_ty_list
          | `Reduce (`RedLeft, red_fn), tt, aa ->
              let out_gr = do_reduc ((`RedLeft, red_fn), tt, aa) hd_c in_gr in
              create_return_nodes out_gr (in_count + 1) (out_count + 1)
                (out_lis @ [ (`Reduce (`RedLeft, red_fn), tt, out_count) ])
                tl_return_action_list tl_mask_ty_list
          | `Reduce (`RedRight, red_fn), tt, aa ->
              let out_gr = do_reduc ((`RedRight, red_fn), tt, aa) hd_c in_gr in
              create_return_nodes out_gr (in_count + 1) (out_count + 1)
                (out_lis @ [ (`Reduce (`RedRight, red_fn), tt, out_count) ])
                tl_return_action_list tl_mask_ty_list
          | `Reduce (`RedTree, red_fn), tt, aa ->
              let out_gr = do_reduc ((`RedTree, red_fn), tt, aa) hd_c in_gr in
              create_return_nodes out_gr (in_count + 1) (out_count + 1)
                (out_lis @ [ (`Reduce (`RedTree, red_fn), tt, out_count) ])
                tl_return_action_list tl_mask_ty_list
          | `Stream_of, tt, aa ->
              assert (tt <> 0);
              let (dd, ee, _), out_gr =
                If1.add_node_2
                  (`Simple
                     ( (If1.STREAM : If1.node_sym),
                       Array.make 1 "",
                       Array.make 1 "",
                       [ If1.No_pragma ] ))
                  out_gr
              in
              let what_ty, out_gr =
                let (id_x, _, _), out_gr =
                  If1.add_type_to_typemap_dedup (If1.Stream tt) out_gr
                in
                (id_x, out_gr)
              in
              let out_gr = If1.add_edge 0 aa dd 0 tt out_gr in
              let out_gr = If1.add_to_boundary_outputs dd ee what_ty out_gr in
              let out_gr =
                match hd_c with
                | Some (aty, pnum) -> If1.add_edge 0 pnum dd 1 aty out_gr
                | None -> out_gr
              in
              create_return_nodes out_gr (in_count + 1) (out_count + 1)
                (out_lis @ [ (`Stream_of, what_ty, out_count) ])
                tl_return_action_list tl_mask_ty_list)
      | _, _ -> raise (If1.Sem_error "Invalid combination for return graph")
    in
    create_return_nodes ret_gr 0 0 [] return_action_list mask_ty_list
  in

  let xyz, in_gr =
    let pragms =
      if prag <> "" then [ If1.Name "RETURNS"; If1.Ast_type prag ]
      else [ If1.Name "RETURNS" ]
    in
    If1.add_node_2 (`Compound (ret_gr, If1.INTERNAL, 0, pragms, [])) in_gr
  in
  (xyz, in_gr, out_lis)

and get_gen_graph in_gr =
  let xyz = find_in_graph_from_pragma in_gr "GENERATOR" in
  match xyz with
  | `Found_one (_, _, _, g, _) -> g
  | `Nth -> raise (If1.Sem_error "Didnt find Generator in In loop")

and get_assoc_list_loopAOrB inner_gr =
  let body_lab =
    let xyz = find_in_graph_from_pragma inner_gr "BODY" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> raise (If1.Sem_error "Didnt find Body in for loop")
  in
  let test_lab =
    let xyz = find_in_graph_from_pragma inner_gr "TEST" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> raise (If1.Sem_error "Didnt find Test in for loop")
  in
  let init_lab =
    let xyz = find_in_graph_from_pragma inner_gr "INIT" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> raise (If1.Sem_error "Didnt find Init in for loop")
  in
  let ret_lab =
    let xyz = find_in_graph_from_pragma inner_gr "RETURNS" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> raise (If1.Sem_error "Didnt find RETURN in for loop")
  in
  [ init_lab; test_lab; body_lab; ret_lab ]

and get_assoc_list inner_gr =
  let gen_lab =
    let xyz = find_in_graph_from_pragma inner_gr "GENERATOR" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> raise (If1.Sem_error "Didnt find Generator in Inner loop")
  in

  let for_lab =
    let xyz = find_in_graph_from_pragma inner_gr "FORALL" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> (
        let xyz = find_in_graph_from_pragma inner_gr "BODY" in
        match xyz with
        | `Nth -> raise (If1.Sem_error "Didnt find Body in Inner loop")
        | `Found_one (lab, _, _, _, _) -> lab)
  in

  let for_returns =
    let xyz = find_in_graph_from_pragma inner_gr "RETURNS" in
    match xyz with
    | `Found_one (lab, _, _, _, _) -> lab
    | `Nth -> raise (If1.Sem_error "Didnt find Returns in Inner loop")
  in
  [ gen_lab; for_lab; for_returns ]

and do_returns_clause in_gr ret_clause =
  match ret_clause with
  | Ast.Old_ret (_, _) -> failwith "DON't KNOW WHAT TO DO HERE"
  | Ast.Return_exp (rexp, mask_clause) ->
      let msk, in_gr =
        match mask_clause with
        | Ast.Unless unless_exp ->
            let in_port_00 = Array.make 1 "" in
            let out_port_00 = Array.make 1 "" in
            let (un, up, uty), in_gr = do_simple_exp in_gr unless_exp in
            let (un_, _, _), in_gr =
              If1.add_node_2
                (`Simple (If1.NOT, in_port_00, out_port_00, []))
                in_gr
            in
            let in_gr = If1.add_edge un up un_ 0 uty in_gr in
            (Some (un_, 0, If1.lookup_tyid If1.BOOLEAN), in_gr)
        | Ast.When when_exp ->
            let when_tup, in_gr = do_simple_exp in_gr when_exp in
            (Some when_tup, in_gr)
        | Ast.No_mask -> (None, in_gr)
      in
      let return_action, node_tup, in_gr = do_return_exp in_gr rexp in
      (return_action, node_tup, msk, in_gr)

and do_returns_clause_list ?(clause_idx = 1) in_gr ret_clause_list
    ret_action_list ret_tuple_list mask_ty_list =
  (* ret_action_list, return_tuple_list, mask_ty_list *)
  match ret_clause_list with
  | hd :: tl ->
      let ret_action, (node_n, node_p, node_t), mask_ty, in_gr =
        do_returns_clause in_gr hd
      in
      let action_str =
        match ret_action with
        | `FinalVal -> "value"
        | `Array_of -> "array_of"
        | `Stream_of -> "stream_of"
        | `Reduce (dir, name) ->
            let dir_str =
              match dir with
              | `JustReduce -> ""
              | `RedLeft -> "/left"
              | `RedRight -> "/right"
              | `RedTree -> "/tree"
            in
            "reduce:" ^ name ^ dir_str
      in
      let mask_str =
        match mask_ty with
        | None -> "no_mask"
        | Some (mn, _, mt) ->
            Printf.sprintf "mask(node=%d,ty=%s)" mn (If1.p_f_t in_gr mt)
      in
      to_if1_msg 3 "returns clause #%d: action=%s node=%d port=%d ty=%s %s"
        clause_idx action_str node_n node_p (If1.p_f_t in_gr node_t) mask_str;
      do_returns_clause_list ~clause_idx:(clause_idx + 1) in_gr tl
        ((ret_action, node_n, node_t) :: ret_action_list)
        ((node_n, node_p, node_t) :: ret_tuple_list)
        (mask_ty :: mask_ty_list)
  | [] -> (in_gr, ret_action_list, ret_tuple_list, mask_ty_list)

and do_defines in_gr = function
  | Ast.Define dn ->
      (* Probably need to fill all externally
        callable functions here *)
      If1.add_each_in_list in_gr dn 0 do_function_name

and is_intrinsic_global fn_name =
  (* Check if a global declaration is for an intrinsic function that is
     already handled via the mangled-name mechanism in intrinsic_lib.
     These do NOT need to be registered in the symtab. *)
  let prefix = Printf.sprintf "_S%s__" (String.uppercase_ascii fn_name) in
  match If1.lookup_partial_mangled_name prefix with
  | Some _ -> true
  | None -> false

and do_global in_gr f =
  let fn_name =
    match f with
    | Ast.Function_header (Ast.Function_name fn, _, _) -> String.concat "." fn
    | Ast.Function_header_nodec (Ast.Function_name fn, _) ->
        String.concat "." fn
  in
  let (_, _, fn_ty), in_gr = do_function_header in_gr f in
  if is_intrinsic_global fn_name then ((0, 0, fn_ty), in_gr)
  else
    let localsyms, globsyms = If1.get_symtab in_gr in
    ( (0, 0, fn_ty),
      {
        in_gr with
        If1.symtab =
          ( localsyms,
            If1.SM.add fn_name
              {
                If1.val_name = fn_name;
                If1.val_ty = fn_ty;
                If1.val_def = 0;
                If1.def_port = 0;
              }
              globsyms );
      } )

and parse_voucher proxy_str =
  match String.split_on_char '#' proxy_str with
  | [ "LINK"; filename; member; "AS"; alias ] -> (filename, member, alias)
  | [ "LINK"; filename; member ] -> (filename, member, "") (* No alias case *)
  | _ ->
      (* Fallback: Not a voucher, just return the name as-is *)
      ("", proxy_str, "")

(* Helper to check if a symbol is a Voucher before we try to redeem it *)
and is_voucher name = String.length name > 5 && String.sub name 0 5 = "LINK#"

and redeem_and_merge_library current_gr voucher_info =
  (* 1. CRACK: LINK#math.sis#Abs#AS#M *)
  let filename, original_name, alias = parse_voucher voucher_info in

  (* 2. ISOLATE: Lower the library into a BRAND NEW graph *)
  let lib_unit = Utils.Slurper.slurp_file filename in
  let {
    If1.nmap = _;
    If1.eset = _;
    If1.symtab = stab;
    If1.typemap = lib_tmap;
    If1.w = _;
  } =
    do_compilation_unit lib_unit
  in

  (* 3. FIND: Locate the specific symbol in the library's finished symtab *)
  let lib_globals, _ = stab in
  let target_info = If1.SM.find_opt original_name lib_globals in
  let target_info =
    match target_info with
    | Some t -> t
    | _ -> failwith ("Symtab missing original name " ^ original_name)
  in

  (* 4. REMAP: If there is an alias (e.g., 'M'), rename the symbol for OUR context *)
  let local_name =
    if alias = "" then original_name else alias ^ "." ^ original_name
  in
  let remapped_info = { target_info with If1.val_name = local_name } in

  (* 5. MERGE: Graft the library's TypeMap and Globals into our current graph *)
  let orig_t_num, tmap, tmn = current_gr.If1.typemap in
  let _, libgr_tmap, _ = lib_tmap in
  let upd_typemap = If1.TM.union (fun _ _ y -> Some y) tmap libgr_tmap in
  let merged_gr =
    {
      current_gr with
      If1.symtab =
        ( If1.SM.add local_name remapped_info (snd (If1.get_symtab current_gr)),
          snd (If1.get_symtab current_gr) );
      If1.typemap = (orig_t_num, upd_typemap, tmn);
    }
  in
  (remapped_info, merged_gr)

and do_compilation_unit = function
  | Ast.Compilation_unit fragments ->
      (* Initialize our empty graph with the standard 7 basic types *)
      let in_gr = If1.get_empty_graph 1 88 in
      (* PASS 1: Register all types, usings, and global signatures across ALL
         fragments before lowering any function body. This ensures mutual
         references between functions in different fragments are visible. *)
      let in_gr =
        List.fold_left
          (fun gr fragment ->
            match fragment with
            | Ast.F_Using (Ast.Using usings) ->
                If1.inject_vouchers_into_symtab gr usings
            | Ast.F_Types type_defs ->
                let (_, _, _), next_gr =
                  If1.add_each_in_list gr type_defs 0 do_typedef
                in
                next_gr
            | Ast.F_Globals globals ->
                let (_, _, _), next_gr =
                  If1.add_each_in_list gr globals 0 do_global
                in
                next_gr
            | Ast.F_Functions _ | Ast.F_Define _ | Ast.F_Skip -> gr)
          in_gr fragments
      in
      (* PASS 2: Lower all function bodies now that all signatures are visible. *)
      let final_gr =
        List.fold_left
          (fun gr fragment ->
            match fragment with
            | Ast.F_Functions fdefs ->
                let (_, _, _), next_gr =
                  If1.add_each_in_list gr fdefs 0 do_function_def
                in
                next_gr
            | Ast.F_Define d ->
                let (_, _, _), gr = do_defines gr d in
                gr
            | Ast.F_Using _ | Ast.F_Types _ | Ast.F_Globals _ | Ast.F_Skip -> gr)
          in_gr fragments
      in

      (* Return our finished graph containing all our IF1 subgraphs *)
      final_gr

and verify_function_returns strs fn_ty_id in_gr =
  let _, tm, _ = If1.get_typemap in_gr in
  (* 1. Extract the Return Tuple ID from the Function Type *)
  let ret_tuple_id =
    match If1.TM.find_opt fn_ty_id tm with
    | Some (Function_ty (_, r, _) as f) ->
        to_if1_msg 3 "verify_returns: fn type=%s sig=%s"
          (If1.p_f_t in_gr fn_ty_id) (If1.string_of_if1_ty f);
        r
    | _ ->
        raise
          (If1.Sem_error
             ("verify_function_returns: fn_ty_id is not a Function_ty for "
            ^ strs))
  in

  (* 2. Flatten the Tuple into a list of expected Type IDs *)
  let rec get_expected_ids tid =
    if tid = 0 then [] (* End of tuple *)
    else
      match If1.TM.find_opt tid tm with
      | Some (Tuple_ty (ty, next)) -> ty :: get_expected_ids next
      | Some _ -> [ tid ] (* Single return value case *)
      | None ->
          raise
            (If1.Sem_error
               ("Missing tuple/type definition for ID: " ^ string_of_int tid))
  in
  let expected_ids = get_expected_ids ret_tuple_id in
  to_if1_msg 3 "verify_returns: expected (%d): [%s]" (List.length expected_ids)
    (String.concat "; "
       (List.mapi
          (fun i tid -> Printf.sprintf "#%d:%s" i (If1.p_f_t in_gr tid))
          expected_ids));

  (* 3. Get the actual edges reaching the boundary node (ID 0) *)
  let actual_edges = If1.all_edges_ending_at_ports_types 0 in_gr in
  to_if1_msg 4 "verify_returns: raw boundary edges (%d): [%s]"
    (List.length actual_edges)
    (String.concat "; "
       (List.map
          (fun (p, ty) -> Printf.sprintf "port%d:%s" p (If1.p_f_t in_gr ty))
          actual_edges));

  (* SEPARATION: Filter out the Railway Monad error ports *)
  (* Only edges with non-ERROR types are treated as logical returns *)
  let data_edges =
    List.filter
      (fun (_, ty_id) -> not (If1.is_error_port ty_id in_gr))
      actual_edges
  in
  to_if1_msg 4 "verify_returns: data boundary edges (%d): [%s]"
    (List.length data_edges)
    (String.concat "; "
       (List.map
          (fun (p, ty) -> Printf.sprintf "port%d:%s" p (If1.p_f_t in_gr ty))
          data_edges));

  (* Sort by port index to ensure we are matching in order *)
  let actual_ids =
    data_edges
    |> List.sort (fun (p1, _) (p2, _) -> compare p1 p2)
    |> List.map snd
  in
  to_if1_msg 3 "verify_returns: actual   (%d): [%s]" (List.length actual_ids)
    (String.concat "; "
       (List.mapi
          (fun i tid -> Printf.sprintf "#%d:%s" i (If1.p_f_t in_gr tid))
          actual_ids));

  (* 4. THE VALIDATION CHECK (Now Error-Blind) *)
  if List.length expected_ids <> List.length actual_ids then
    raise
      (If1.Sem_error
         (If1.If1_View.export_debug_html "CRASHED.html" in_gr;
          Printf.sprintf
            "Return Arity Mismatch: Header expects %d data values, but graph \
             returns %d (excluding errors)"
            (List.length expected_ids) (List.length actual_ids)))
  else
    List.fold_left2
      (fun idx exp act ->
        (if exp <> act then
           let tm = If1.get_typemap_tm in_gr in
           match (If1.TM.find_opt exp tm, If1.TM.find_opt act tm) with
           | Some ty_exp, Some ty_act ->
               if ty_exp <> ty_act then
                 (* Allow numeric type mismatches (widening/narrowing between numeric families) *)
                 let is_numeric_compat =
                   match (numeric_rank exp in_gr, numeric_rank act in_gr) with
                   | Some _, Some _ -> true
                   | _ -> false
                 in
                 if not is_numeric_compat then (
                   (* Check if the mismatch is due to an unexpected Error Type *)
                   let err_msg =
                     match ty_act with
                     | ERROR s ->
                         Printf.sprintf
                           "return value #%d: Hardware Trap/Error found: %s" idx
                           s
                     | _ ->
                         Printf.sprintf
                           "return value #%d: Expected %s (#%d), but found %s \
                            (#%d)"
                           idx
                           (If1.printable_full_type (If1.get_typemap_tm in_gr)
                              exp)
                           exp
                           (If1.printable_full_type (If1.get_typemap_tm in_gr)
                              act)
                           act
                   in
                   (*print_endline (If1.str_type_trace ()); *)
                   If1.If1_View.export_debug_html "CRASHED.html" in_gr;
                   raise (If1.Sem_error ("Return Type Mismatch: " ^ err_msg)))
           | _ ->
               raise
                 (If1.Sem_error
                    (Printf.sprintf
                       "Return Type Mismatch: return value #%d: type ID %d or \
                        %d not found in typemap"
                       idx exp act)));
        idx + 1)
      1 expected_ids actual_ids
    |> ignore;
  (*
if List.length expected_ids <> List.length actual_ids then (
    If1_JSON.export_to_json "compiler_crash.json" in_gr;
    Printf.printf "\n[CRITICAL] Arity mismatch! State saved to compiler_crash.json\n%!";
    raise (If1.Sem_error "Return Arity Mismatch")
)
  print_endline
    "VALIDATION SUCCESS: Data results match signature (Railway errors ignored)."
     *)

and do_typedef in_gr = function
  | Type_def (n, t) ->
      (* 1. Placeholder binding *)
      let _, in_gr = If1.add_sisal_typename in_gr n (-2) in

      (* 2. Incremental Lowering *)
      let (id_t, ii, tt), in_gr = If1.add_sisal_type in_gr t in

      (* 3. Update the name map MM.t *)
      let id_, in_gr = If1.add_sisal_typename in_gr n tt in

      (* 4. DEEP PATCHING: Replace ALL occurrences of -2 (the placeholder) with
         the actual type ID `tt` throughout the entire typemap. The targeted
         single-entry patch missed nested references — e.g. for a recursive
         type like  type Radical = union[...; Carbon: array[Radical]]
         the Array_ty(-2) entry is a sibling in the typemap, not a child of
         the union head, so it was never patched. *)
      let next_id, tm, mm = in_gr.typemap in
      let patch id = if id = -2 then tt else id in
      let patch_ty = function
        | If1.Record (a, b, s) -> If1.Record (patch a, patch b, s)
        | If1.Union (a, b, s) -> If1.Union (patch a, patch b, s)
        | If1.Function_ty (a, b, s) -> If1.Function_ty (patch a, patch b, s)
        | If1.Array_ty a -> If1.Array_ty (patch a)
        | If1.Stream a -> If1.Stream (patch a)
        | If1.Tuple_ty (a, b) -> If1.Tuple_ty (patch a, patch b)
        | If1.Field ls -> If1.Field (List.map patch ls)
        | If1.Tag ls -> If1.Tag (List.map patch ls)
        | If1.Typed_error a -> If1.Typed_error (patch a)
        | other -> other
      in
      let tm = If1.TM.map patch_ty tm in
      let final_gr = { in_gr with If1.typemap = (next_id, tm, mm) } in
      ((id_t, ii, id_), final_gr)

and do_internals (names, in_gr) f =
  match f with
  | [] -> (names, in_gr)
  | Ast.Function_single (header, tdefs, nest, e) :: tl ->
      let fn_name =
        match header with
        | Ast.Function_header_nodec (Ast.Function_name fn, _) -> fn
        | Ast.Function_header (Ast.Function_name fn, _, _) -> fn
      in
      let (_, _, fn_ty), new_fun_gr_ =
        do_function_header
          (If1.inherit_parent_syms in_gr (If1.get_a_new_graph in_gr))
          header
      in
      let localsyms, globsyms = If1.get_symtab in_gr in
      let in_gr =
        {
          in_gr with
          If1.symtab =
            ( If1.SM.add
                (String.concat "." fn_name)
                {
                  If1.val_name = String.concat "." fn_name;
                  If1.val_ty = fn_ty;
                  If1.val_def = 0;
                  (* these are unknown at this time *)
                  If1.def_port = 0;
                }
                localsyms,
              globsyms );
        }
      in
      let localsyms, globsyms = If1.get_symtab new_fun_gr_ in
      let new_fun_gr_ =
        {
          new_fun_gr_ with
          If1.symtab =
            ( localsyms,
              If1.SM.add
                (String.concat "." fn_name)
                {
                  If1.val_name = String.concat "." fn_name;
                  If1.val_ty = fn_ty;
                  If1.val_def = 0;
                  (* these are unknown at this time *)
                  If1.def_port = 0;
                }
                globsyms );
        }
      in
      let (_, _, _), new_fun_gr_ =
        If1.add_each_in_list new_fun_gr_ tdefs 0 do_typedef
      in
      let _, new_fun_gr_ =
        If1.add_each_in_list new_fun_gr_ nest 0 do_function_def
      in
      let new_fun_gr_ =
        let (frm, elp, elt), new_fun_gr_ = do_exp new_fun_gr_ e in
        point_edges_to_boundary frm elp elt new_fun_gr_
      in
      let new_fun_gr_ = If1.graph_clean_multiarity new_fun_gr_ in
      let () =
        let strs = Ast.internals 1 f in
        to_if1_msg 2 "verify_returns: function %s" (String.concat "." fn_name);
        verify_function_returns strs fn_ty new_fun_gr_
      in
      let (aa, bb, _), in_gr =
        If1.add_node_2
          (`Compound
             ( new_fun_gr_,
               If1.INTERNAL,
               0,
               [
                 If1.Name (String.concat "." fn_name);
                 If1.Ast_type (Ast.internals 0 f);
               ],
               [] ))
          in_gr
      in
      let in_gr =
        let localsyms, globsyms = If1.get_symtab in_gr in
        {
          in_gr with
          If1.symtab =
            ( If1.SM.add
                (String.concat "." fn_name)
                {
                  If1.val_name = String.concat "." fn_name;
                  If1.val_ty = fn_ty;
                  If1.val_def = aa;
                  If1.def_port = bb;
                }
                localsyms,
              globsyms );
        }
      in
      do_internals (names @ [ fn_name ], in_gr) tl

and do_function_def in_gr = function
  | Ast.Function f ->
      let _, in_gr_ = do_internals ([], in_gr) f in
      ((0, 0, 0), in_gr_)
  | Forward_function f ->
      let fn_name =
        match f with
        | Ast.Function_header_nodec (Ast.Function_name fn, _) ->
            String.concat "." fn
        | Ast.Function_header (Ast.Function_name fn, _, _) ->
            String.concat "." fn
      in
      let (_, _, fn_ty), in_gr = do_function_header in_gr f in
      let localsyms, globsyms = If1.get_symtab in_gr in
      ( (0, 0, fn_ty),
        {
          in_gr with
          If1.symtab =
            ( If1.SM.add fn_name
                {
                  If1.val_name = fn_name;
                  If1.val_ty = fn_ty;
                  If1.val_def = 0;
                  If1.def_port = 0;
                }
                localsyms,
              globsyms );
        } )

and do_function_header in_gr = function
  | Ast.Function_header_nodec (fn, tl) ->
      let _, in_gr = do_function_name in_gr fn in
      If1.add_sisal_type in_gr
        (Ast.Compound_type (Ast.Sisal_function_type ("", [], tl)))
  | Ast.Function_header (Ast.Function_name fn, decls, tl) ->
      let nm = in_gr.If1.nmap in
      let nm =
        If1.NM.add 0
          (let bound_node = If1.NM.find_opt 0 nm in
           match bound_node with
           | Some (If1.Boundary (k, j, e, p)) ->
               If1.Boundary (k, j, e, If1.Name (String.concat "." fn) :: p)
           | _ -> failwith "Boundary node missing in graph")
          nm
      in
      let in_gr = { in_gr with If1.nmap = nm } in
      let tyy = extract_types_from_decl_list decls in
      let _, (_, _, _), in_gr =
        let rec addeach_decl in_gr decls lasti bi q =
          match decls with
          | [] -> (bi, (lasti, q, 0), in_gr)
          | hde :: tl ->
              let (lasti, pp, tt1), in_gr = do_params_decl lasti in_gr hde in
              addeach_decl in_gr tl lasti ((lasti, pp, tt1) :: bi) pp
        in
        addeach_decl in_gr decls 0 [] []
      in
      If1.add_sisal_type in_gr
        (Ast.Compound_type
           (Ast.Sisal_function_type (String.concat "." fn, tyy, tl)))

let _ = do_compilation_unit
