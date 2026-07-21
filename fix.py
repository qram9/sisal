import sys
import re

def fix():
    with open('src/to_if1/to_if1.ml', 'r') as f:
        content = f.read()

    # 1. Non-exhaustive match fix
    content = content.replace('| Ast.Catenate -> "catenate"', '| Ast.Catenate -> "catenate" | Ast.Argmax -> "argmax" | Ast.Argmin -> "argmin"')

    # 2. find_in_graph_from_pragma fix
    pattern_find = r'and find_in_graph_from_pragma in_gr namen =.*?(?=and |let rec |val |let \(\*.*\*\))'
    replacement_find = """and find_in_graph_from_pragma in_gr namen =
  let nm = in_gr.If1.nmap in
  If1.NM.fold (fun lab node acc ->
    match acc with
    | `Found_one _ -> acc
    | `Nth -> (
        match node with
        | If1.Compound (lab, sy, ty, pl, g, assoc) ->
            if List.exists (function If1.Name s -> s = namen | _ -> false) pl
            then `Found_one (lab, sy, pl, g, assoc)
            else acc
        | _ -> acc
      )
  ) nm `Nth

"""
    content = re.sub(pattern_find, replacement_find, content, flags=re.DOTALL)

    # 3. For_initial overhaul
    # We find the start of the loopAOrB match and replace the entire function
    start_pattern = r'      let loopAOrB i in_gr =.*?((mul_n, mul_p, ty), in_gr)'
    replacement_loop = """      let loopAOrB i in_gr =
        match i with
        | Ast.Iterator_termination (ii, t) ->
            to_if1_msg 3 "LoopA: building INIT decls";
            let (_, decl_gr, _) = add_decls in_gr d in
            to_if1_msg 3 "LoopA: building BODY iterator: %s" (Ast.str_iterator ii);
            let body_gr, return_action_list, _, mask_ty_list = add_body decl_gr ii r in
            to_if1_msg 3 "LoopA: building TEST termination: %s" (Ast.str_termination t);
            let (_, _, _), test_gr = add_terminator body_gr t in
            to_if1_msg 3 "LoopA: building RETURNS (%d clauses)" (List.length return_action_list);
            let (_, _, _), for_gr, return_action_list = add_ret body_gr return_action_list mask_ty_list
                (String.concat "\\n" (List.map Ast.str_return_clause r)) in
            let _, for_gr = add_comp_node body_gr "BODY" for_gr in
            let _, for_gr = add_comp_node test_gr "TEST" for_gr in
            let _, for_gr = add_comp_node decl_gr "INIT" for_gr in
            let for_gr = get_ports_unified for_gr body_gr decl_gr in
            let (fx, _, _), in_gr = If1.add_node_2 (`Compound (for_gr, If1.INTERNAL, 0,
                     [ If1.Name "LoopA"; If1.Compound_of If1.If1_loop_initial; If1.Ast_type (Ast.str_simple_exp finit) ],
                     let lis = get_assoc_list_loopAOrB for_gr in List.length lis :: lis )) in_gr in
            let _, in_gr = wire_all_syms_to_compound fx for_gr in_gr in
            let (mul_n, mul_p, mul_t), in_gr = build_multiarity (List.length return_action_list) in_gr ~nam:"FOR_INITIAL_LOOP_A" in
            let _, outl, in_gr = List.fold_left (fun (cc, outl, iigr) (wh, tt, aa) ->
                  ( cc + 1, outl @ [ (wh, tt, fx, cc) ], If1.add_edge2 fx aa mul_n cc tt iigr ))
                (0, [], in_gr) return_action_list in
            ((mul_n, mul_p, mul_t), outl, in_gr)
        | Termination_iterator (t, ii) ->
            to_if1_msg 3 "LoopB: creating Activation Frame (for_gr)";
            let for_gr = If1.get_a_new_graph in_gr in
            let (_, decl_gr, carry_init_map) = add_decls for_gr d in
            let (true_n, true_p, true_t), decl_gr = do_simple_exp decl_gr (Ast.Constant Ast.True) in
            let ctrl_init_out_p = If1.boundary_out_port_count decl_gr in
            let decl_gr = If1.output_to_boundary ~start_port:ctrl_init_out_p [(true_n, true_p, true_t)] decl_gr in
            let ctrl_port_in, for_gr = If1.add_to_boundary_inputs ~namen:"LOOP_CTRL" 0 0 for_gr in
            let for_gr, carry_merge_map = 
              List.fold_left (fun (gr, acc) (nm, icp, iop, ty) ->
                let (mn_c, mp_c, _), gr = If1.add_node_2 (`Simple (If1.MERGE, [|"" ;"" ;""|], [|""|], [])) gr in
                let (mn_o, mp_o, _), gr = If1.add_node_2 (`Simple (If1.MERGE, [|"" ;"" ;""|], [|""|], [])) gr in
                let gr = If1.add_edge 0 ctrl_port_in mn_c 0 (If1.lookup_tyid If1.BOOLEAN) gr in
                let gr = If1.add_edge 0 ctrl_port_in mn_o 0 (If1.lookup_tyid If1.BOOLEAN) gr in
                let gr = If1.bind_name nm (mn_c, mp_c, ty) gr in
                let gr = If1.bind_name ("OLD " ^ nm) (mn_o, mp_o, ty) gr in
                (gr, (nm, mn_c, mp_c, mn_o, mp_o, ty) :: acc)
              ) (for_gr, []) carry_init_map in
            let (_, _, _), test_gr = add_terminator for_gr t in
            let body_gr, return_action_list, ret_tuple_list, mask_ty_list = add_body for_gr ii r in
            let init_cx, for_gr = add_comp_node decl_gr "INIT" for_gr in
            let body_cx, for_gr = add_comp_node body_gr "BODY" for_gr in
            let test_cx, for_gr = add_comp_node test_gr "TEST" for_gr in
            let for_gr = List.fold_left (fun gr (nm, icp, iop, ty) ->
                let (_, mnc, mpc, mno, mpo, _) = List.find (fun (n,_,_,_,_,_) -> n = nm) carry_merge_map in
                let gr = If1.add_edge init_cx icp mnc 1 ty gr in
                let gr = If1.add_edge init_cx iop mno 1 ty gr in
                gr
            ) for_gr carry_init_map in
            let for_gr = If1.add_edge init_cx ctrl_init_out_p 0 ctrl_port_in (If1.lookup_tyid If1.BOOLEAN) for_gr in
            let body_gr, feedback_map, _ = 
                let next_p = If1.boundary_out_port_count body_gr in
                List.fold_left (fun (gr, acc, p) (nm, mnc, mpc, mno, mpo, ty) ->
                    let feed_c = match If1.SM.find_opt nm (fst gr.If1.symtab) with
                        | Some entry -> (entry.If1.val_def, entry.If1.def_port, entry.If1.val_ty)
                        | None -> (mnc, mpc, ty) in
                    let feed_o = (mnc, mpc, ty) in
                    let gr = If1.output_to_boundary ~start_port:p [feed_c; feed_o] gr in
                    (gr, (nm, p, p+1) :: acc, p + 2)
                ) (body_gr, [], next_p) carry_merge_map in
            let (false_n, false_p, false_t), body_gr = do_simple_exp body_gr (Ast.Constant Ast.False) in
            let ctrl_feed_p = If1.boundary_out_port_count body_gr in
            let body_gr = If1.output_to_boundary ~start_port:ctrl_feed_p [(false_n, false_p, false_t)] body_gr in
            let for_gr = { for_gr with If1.nmap = If1.NM.add body_cx 
                (match If1.NM.find body_cx for_gr.If1.nmap with
                 | If1.Compound (l, s, t, p, _, a) -> If1.Compound (l, s, t, p, body_gr, a)
                 | x -> x) for_gr.If1.nmap } in
            let for_gr = List.fold_left (fun gr (nm, fcp, fop) ->
                let (_, mnc, mpc, mno, mpo, ty) = List.find (fun (n,_,_,_,_,_) -> n = nm) carry_merge_map in
                let gr = If1.add_edge body_cx fcp mnc 2 ty gr in
                let gr = If1.add_edge body_cx fop mno 2 ty gr in
                gr
            ) for_gr feedback_map in
            let for_gr = If1.add_edge body_cx ctrl_feed_p 0 ctrl_port_in (If1.lookup_tyid If1.BOOLEAN) for_gr in
            let (ret_cx, _, _), for_gr, return_action_list_final = 
                add_ret for_gr return_action_list mask_ty_list (String.concat "\\n" (List.map Ast.str_return_clause r)) in
            let (ret_cx_real, for_gr) = add_comp_node (match If1.NM.find ret_cx for_gr.If1.nmap with If1.Compound(_,_,_,_,g,_) -> g | _ -> for_gr) "RETURNS" for_gr in
            let (fx, _, _), in_gr = If1.add_node_2 (`Compound (for_gr, If1.INTERNAL, 0,
                     [ If1.Name "LoopB"; If1.Compound_of If1.If1_loop_initial; If1.Ast_type (Ast.str_simple_exp finit) ],
                     let lis = get_assoc_list_loopAOrB for_gr in List.length lis :: lis )) in_gr in
            let _, in_gr = wire_all_syms_to_compound fx for_gr in_gr in
            let (mul_n, mul_p, mul_t), in_gr = build_multiarity (List.length return_action_list_final) in_gr ~nam:"FOR_INITIAL_LOOP_B" in
            let _, outl, in_gr = List.fold_left (fun (cc, outl, iigr) (wh, tt, aa) ->
                  ( cc + 1, outl @ [ (wh, tt, fx, cc) ], If1.add_edge2 fx aa mul_n cc tt iigr ))
                (0, [], in_gr) return_action_list_final in
            ((mul_n, mul_p, mul_t), outl, in_gr)
      in
      let (mul_n, mul_p, ty), in_gr = 
          let (mn, mp, _), ret_actions, ig = loopAOrB i in_gr in
          let ty = match ret_actions with (_, arr_ty, _, _) :: _ -> arr_ty | _ -> 0 in
          ((mn, mp, ty), ig)
      in
      ((mul_n, mul_p, ty), in_gr)"""
    content = re.sub(start_pattern, replacement_loop, content, flags=re.DOTALL)

    # 4. Helper refactoring (add_comp_node)
    old_comp = r'let add_comp_node in_gr namen \?\(prag = ""\) to_gr =.*?verify_compound_inputs cn in_gr on;\s+on\s+in'
    new_comp = """let add_comp_node in_gr namen to_gr =
        let c_of = match namen with
          | "INIT" -> If1.If1_loop_initial
          | "TEST" -> If1.If1_loop_test
          | "BODY" -> If1.If1_body
          | "RETURNS" -> If1.If1_results
          | _ -> If1.If1_Unknown in
        let prags = [ If1.Name namen; If1.Compound_of c_of ] in
        let (cn, _, _), on = If1.add_node_2 (`Compound (in_gr, If1.INTERNAL, 0, prags, [])) to_gr in
        let _, on = wire_all_syms_to_compound cn in_gr on in
        (cn, on)
      in
"""
    content = re.sub(old_comp, new_comp, content, flags=re.DOTALL)

    # 5. add_decls refactor (to return carry_init_map)
    old_decls = r'let add_decls in_gr dp =.*?\(xyz, out_gr\)\s+in'
    new_decls = """let add_decls in_gr dp =
        let build_init_graph in_gr = get_ports_unified (If1.get_a_new_graph in_gr) in_gr in_gr in
        let xyz, out_gr = do_decldef_part (build_init_graph in_gr) dp in
        let _, out_gr, carry_init_map =
          let cs, ps = out_gr.If1.symtab in
          If1.SM.fold
            (fun nm entry (op, gr, acc) ->
              if If1.SM.mem nm ps then (op, gr, acc)
              else
                let t1, dd, dp = entry.If1.val_ty, entry.If1.val_def, entry.If1.def_port in
                let gr = If1.add_edge dd dp 0 op t1 gr in
                let gr = If1.add_edge dd dp 0 (op + 1) t1 gr in
                let acc = (nm, op, op + 1, t1) :: acc in
                (op + 2, gr, acc))
            cs (0, out_gr, [])
        in
        (xyz, out_gr, List.rev carry_init_map)
      in
"""
    content = re.sub(old_decls, new_decls, content, flags=re.DOTALL)

    with open('src/to_if1/to_if1.ml', 'w') as f:
        f.write(content)
    print("Success")

if __name__ == '__main__':
    fix()
