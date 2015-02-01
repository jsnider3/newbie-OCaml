module Interpreter :
  sig
    type kind =
        TInt
      | TReal
      | TBool
      | TChar
      | TFunc of (kind * kind)
      | TTuple of kind list
      | TyL of kind
      | TyR of kind
      | TList of (kind * int)
      | TRecord of (string * kind) list
      | TUnit
      | TSum of (kind * kind)
      | TTop
      | TBottom
      | TStr
    type expr =
        N of int
      | F of float
      | Add of (expr * expr)
      | Mul of (expr * expr)
      | Sub of (expr * expr)
      | And of (expr * expr)
      | Or of (expr * expr)
      | Not of expr
      | If of (expr * expr * expr)
      | Equal of (expr * expr)
      | B of bool
      | Lam of (kind * string * expr)
      | App of (expr * expr)
      | Var of string
      | Tuple of expr list
      | List of (expr * expr)
      | Unit
      | Concat of (expr * expr)
      | Get of (expr * expr)
      | Head of expr
      | Tail of expr
      | Record of (string * expr) list
      | GetRec of (string * expr)
      | Fix of expr
      | LetN of ((string * expr) list * expr)
      | TL of expr
      | TR of expr
      | Case of (expr * expr * expr)
      | As of (expr * kind)
      | Seq of expr list
      | Set of (kind * string * expr)
      | Lookup of string
      | While of (expr * expr)
      | Top
      | Bottom
      | C of char
    type value =
        VB of bool
      | VC of char
      | VTuple of value list
      | VList of (value * value)
      | VUnit
      | VL of value
      | VR of value
      | VN of int
      | VF of float
      | VLam of expr
      | VRecord of (string * expr) list
      | VTop
      | VBottom
    type env_type = (string, value) Core.Std.Hashtbl.t
    type type_map = (string, kind) Core.Std.Hashtbl.t
    val subtype : kind -> kind -> bool
    val common_type : kind -> kind -> kind
    val echo_first : 'a -> 'b -> 'a
    val typecheck : expr -> (string, kind) Core.Std.Hashtbl.t -> kind
    val typecheck_case :
      expr * expr * expr -> (string, kind) Core.Std.Hashtbl.t -> kind
    val typecheck_as :
      expr * kind -> (string, kind) Core.Std.Hashtbl.t -> kind
    val subst : string -> expr -> expr -> expr
    val make_expr : value -> expr
    val eval : expr -> (string, value) Core.Std.Hashtbl.t -> value
    val exec : expr -> value
  end
