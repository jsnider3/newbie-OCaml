type expr;
type value;
type kind;
type env_type = (string, int) Hashtbl.t;;
val	typecheck : expr -> env_type ->kind
val	common_type : kind -> kind -> kind
val sub_type : kind -> kind -> bool
val lookup_type : string -> env_type -> kind
val purge_env : env_type -> expr -> env_type (* Suspicious. *)
val free : (string, kind) -> env_type -> bool (* Suspicious *)
val simplify_type : kind -> kind
val exec : expr -> value
val subst : string -> expr -> expr
val eval : expr -> value
val set_helper : (string, value) -> env_type -> bool (* Probably unnecessary TODO: Remove*)
val lookup_state : string -> env_type -> value
val make_expr : value -> expr (* Sloppy. TODO: Try removing *)

