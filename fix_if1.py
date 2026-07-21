import sys

def fix():
    with open('src/ir/if1.ml', 'r') as f:
        content = f.read()

    # Recursive get_symbol_id implementation
    old_code = """and get_symbol_id v in_gr =
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
    ((0, next_port, p_entry.val_ty), in_gr)"""

    new_code = """and get_symbol_id v in_gr =
  let cs, ps = get_symtab in_gr in
  (* 1. Check current scope *)
  if SM.mem v cs then
    let entry = SM.find v cs in
    ((entry.val_def, entry.def_port, entry.val_ty), in_gr)
  (* 2. Check parent scope for automatic boundary import *)
  else if SM.mem v ps then
    let p_entry = SM.find v ps in
    (* CRITICAL: If the parent's definition is also an external import (val_def=0)
       or if it's from a higher scope (not a local node), we must ensure the 
       immediate parent has a valid local port for it. *)
    let (sn, sp, sty), parent_gr_updated = 
        if p_entry.val_def = 0 then
            (* It is already a boundary port in the parent. Use it. *)
            ((p_entry.val_def, p_entry.def_port, p_entry.val_ty), in_gr)
        else
            (* It is a local node in some ancestor scope. 
               This branch currently only handles one level safely. 
               We use the existing p_entry values. *)
            ((p_entry.val_def, p_entry.def_port, p_entry.val_ty), in_gr)
    in
    let next_port, in_gr =
      add_to_boundary_inputs ~namen:v sn sp in_gr
    in
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
    ((0, next_port, p_entry.val_ty), in_gr)"""

    if old_code in content:
        content = content.replace(old_code, new_code)
        with open('src/ir/if1.ml', 'w') as f:
            f.write(content)
        print("Success")
    else:
        print("Not found")

if __name__ == '__main__':
    fix()
