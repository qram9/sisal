(** Builds type equivalence classes for the IF1 typemap.
  Returns a tuple containing:
  1. A TM.t mapping every original type ID (alias) to its equivalence class leader ID.
  2. A new if1_ty TM.t containing only the unique leader types.
*)
let build_type_equivalence_classes in_gr =
  let _, tm, _ = If1.get_typemap in_gr in
  
  (* Fold over the existing typemap to group by structural equality *)
  let alias_map, leaders =
    If1.TM.fold (fun id ty (acc_alias, acc_leaders) ->
      (* Check if the current type matches any already established leader *)
      let matching_leader =
        List.find_opt (fun (_, leader_ty) ->
          (* Use the existing structurally_equal function with an empty 'seen' list *)
          If1.structurally_equal in_gr [] ty leader_ty
        ) acc_leaders
      in
      
      match matching_leader with
      | Some (leader_id, _) ->
          (* It matches an existing leader, map this ID to the leader's ID *)
          (If1.TM.add id leader_id acc_alias, acc_leaders)
      | None ->
          (* No match found, so this type becomes a new class leader *)
          (If1.TM.add id id acc_alias, (id, ty) :: acc_leaders)
          
    ) tm (If1.TM.empty, [])
  in
  
  (* Construct the new TM.t exclusively from the leaders *)
  let new_tm =
    List.fold_left (fun acc (l_id, l_ty) ->
      If1.TM.add l_id l_ty acc
    ) If1.TM.empty leaders
  in
  
  (alias_map, new_tm)
(** Updates the val_ty field for all entries in a symbol table map 
    using the provided alias_map (which maps old type IDs to leader IDs). *)
let update_symtab_types alias_map symtab =
  If1.SM.map (fun sym_val ->
    (* Look up the current type ID in the alias map to find its leader *)
    let leader_ty = 
      match If1.TM.find_opt sym_val.If1.val_ty alias_map with
      | Some leader_id -> leader_id
      | None -> sym_val.val_ty (* Fallback to original if not in map *)
    in
    (* Return a new record with the updated type ID *)
    { sym_val with val_ty = leader_ty }
  ) symtab
(** Updates both the local and parent symbol tables in the graph's symtab tuple *)
let update_graph_symtab alias_map (local_syms, parent_syms) =
  let new_local_syms = update_symtab_types alias_map local_syms in
  let new_parent_syms = update_symtab_types alias_map parent_syms in
  (new_local_syms, new_parent_syms)
(** Updates the type IDs of all edges in an edge set using the alias_map. *)
let update_edge_types alias_map eset =
  If1.ES.fold (fun ((src_n, src_p), (dst_n, dst_p), ty_id) acc_eset ->
    (* Look up the edge's current type ID to find its leader *)
    let leader_ty_id =
      match If1.TM.find_opt ty_id alias_map with
      | Some leader_id -> leader_id
      | None -> ty_id (* Fallback if not found, though ideally it should be *)
    in
    
    (* Add the edge with the updated type ID to the new set *)
    If1.ES.add ((src_n, src_p), (dst_n, dst_p), leader_ty_id) acc_eset
    
  ) eset If1.ES.empty


(** Helper to apply the edge type update to the entire graph *)
let update_graph_edges alias_map in_gr =
  let updated_eset = update_edge_types alias_map in_gr.If1.eset in
  { in_gr with eset = updated_eset }

(** Removes structural type duplicates and updates all references in the graph. *)
let deduplicate_graph_types in_gr =
  (* 1. Build the equivalence classes and the new deduplicated typemap *)
  let alias_map, new_tm = build_type_equivalence_classes in_gr in
  
  (* 2. Update the local and parent symbol tables *)
  let updated_symtab = update_graph_symtab alias_map in_gr.symtab in
  
  (* 3. Update the edge set *)
  let updated_eset = update_edge_types alias_map in_gr.eset in
  
  (* 4. Reconstruct and return the fully updated graph *)
  let id, _, tmn = If1.get_typemap in_gr in
  { in_gr with 
    If1.eset = updated_eset;
    symtab = updated_symtab;
    typemap = (id, new_tm, tmn) (* Keep the string name map & ID counter, swap the TM.t *)
  }
