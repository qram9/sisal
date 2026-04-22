open Ir.If1
module C = Ir.C_ast

let translate (gr : graph) : C.translation_unit = Apple_lower.translate gr
