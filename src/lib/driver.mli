type env

type output =
  | Def of Concrete_syntax.ident * Syntax.t * Syntax.t * env
  | NF_term of Syntax.t * Syntax.t
  | NF_def of Concrete_syntax.ident * Syntax.t
  | Quit


val output : env -> output -> unit
val update_env : env -> output -> env

val process_sign : ?env:env -> Concrete_syntax.signature -> env
val print_unsolved_holes : env -> unit
