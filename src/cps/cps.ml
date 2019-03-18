
module CPS : sig
  type var = V
  type value = VAR of var
             | LABEL of var
             | INT of int
             | REAL of string
             | STRING of string
  type accesspath = OFFp of int
                  | SELp of int * accesspath
  type primop = 
    Star | Plus | Minus | Div | Not 
    | Ieql | Ineq | Less | Lesseq | Greater | Greatereq | Rangechk
    | Bang | Subscript | Ordof | Coloneq | Unboxedassign | Update | Unboxedupdate | Store
    | Makeref | Makerefunboxed | Alength | Slength 
    | Gethdlr | Sethdlr | Boxed | Fadd | Fsub | Fdiv | Fmul
    | Feql | Fneq | Fge | Fgt | Fle | Flt
    | Rshift | Lshift | Orb | Andb | Xorb | Notb

  type cexp = 
    RECORD of (value * accesspath) list * var * cexp
    | SELECT of int * value * var * cexp
    | OFFSET of int * value * var * cexp
    | APP of value * value list
    | FIX of (var * var list * cexp) list * cexp
    | SWITCH of value * cexp list
    | PRIMOP of primop * value list * var list * cexp list
  val hello : unit -> unit
end =
struct
  let message = "Hello"
  let hello() = print_endline message
end
