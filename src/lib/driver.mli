type env

(* type check_output = *)
(*   | CheckedDef of Concrete_syntax.ident * Syntax.t * Syntax.t * env *)
(*   | NF_term of Syntax.t * Syntax.t *)
(*   | NF_def of Concrete_syntax.ident * Syntax.t *)
(*   | Quit *)

type elab_output
type check_output

val update_env : env -> check_output -> env

val process_sign : ?env:env -> Concrete_syntax.signature -> env
val print_unsolved_holes : env -> unit
