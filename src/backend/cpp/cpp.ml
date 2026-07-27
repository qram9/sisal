(** cpp.ml: Primary entry point for the C++ code-generation backend.
    This module bridges the IF1 intermediate representation and the C++
    lowering pass.  (Portable C++23; Apple's Accelerate/GCD are opt-in, guarded
    by __APPLE__ in the emitted code and the runtime.) *)

open Ir.If1
module C = Ir.C_ast

(** [translate gr] initiates the translation of an IF1 graph [gr] into a C++
    Abstract Syntax Tree (C-AST), delegating the heavy lifting to the
    [Cpp_lower] module. *)
let translate (gr : graph) : C.translation_unit =
  let _, tm, _ = gr.typemap in
  Cpp_lower.lower_to_c tm gr "out.cpp"
