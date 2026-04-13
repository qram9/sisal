(** 
  C-AST: A modern, functional IR for C/C++ code generation.
  Modernized for "Apple Lowering" targeting M4 Max silicon.
*)

type qualifier = Const | Volatile | Restrict

type c_type =
  | Basic of string
  | Pointer of c_type * qualifier list
  | Array of c_type * int option
  | Vector of c_type * int                (** SIMD: __attribute__((vector_size(N))) *)
  | Struct of string * (string * c_type) list
  | Union of string * (string * c_type) list
  | Void

type binary_op = 
  | Add | Sub | Mul | Div | Mod
  | Shl | Shr
  | BitAnd | BitOr | BitXor
  | LogAnd | LogOr
  | Eq | Ne | Lt | Le | Gt | Ge
  | Assign
  | AssignAdd | AssignSub | AssignMul | AssignDiv

type unary_op =
  | PreInc | PostInc | PreDec | PostDec
  | AddrOf | Deref
  | Negate | BitNot | LogNot

type expr =
  | Id of string
  | LitInt of int
  | LitFloat of float
  | LitString of string
  | BinOp of binary_op * expr * expr
  | UnaryOp of unary_op * expr
  | Call of string * expr list
  | Index of expr * expr
  | Member of expr * string
  | Arrow of expr * string
  | Cast of c_type * expr
  | Cond of expr * expr * expr

type stmt =
  | Decl of c_type * string * expr option
  | Expr of expr
  | For of stmt * expr * expr * stmt list
  | While of expr * stmt list
  | DoWhile of stmt list * expr
  | If of expr * stmt list * stmt list
  | Return of expr option
  | Break
  | Continue
  | Pragma of string
  | GCDApply of expr * string * (string * stmt list)
  | MetalKernel of {
      name: string;
      params: (c_type * string * int) list;
      body: stmt list;
    }
  | Compound of stmt list
  | Comment of string

type procedure = {
  return_ty: c_type;
  name: string;
  params: (c_type * string) list;
  body: stmt list;
  extern_c: bool;
}

type translation_unit = {
  filename: string;
  includes: string list;
  globals: stmt list;
  procedures: procedure list;
}
