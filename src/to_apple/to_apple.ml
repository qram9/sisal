(** to_apple.ml: Primary entry point for the Apple Silicon (M4 Max) backend.
    This module serves as a bridge between the IF1 intermediate representation
    and the specialized Apple lowering pass. *)

open Ir.If1
module C = Ir.C_ast

(** [translate gr] initiates the translation of an IF1 graph [gr] into a C
    Abstract Syntax Tree (C-AST) optimized for Apple Silicon, delegating the
    heavy lifting to the [Apple_lower] module. *)
let translate (gr : graph) : C.translation_unit = Apple_lower.translate gr
