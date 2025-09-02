open Mode_theory

(* val env_to_sem_env : Meta.Check_env.env -> Domain.env *)

type error =
  | Cannot_synth_term of Syntax.t
  | Type_mismatch of Syntax.t * Syntax.t * Syntax.t
  | Term_or_Type_mismatch of Syntax.t * Syntax.t
  | Expecting_universe of Syntax.t
  | Modality_mismatch of m * m * Syntax.t * Syntax.t
  | Mode_mismatch of mode * mode * Syntax.t
  | Cell_fail of m * m * Syntax.t * Syntax.t
  | Misc of string

val pp_error : error -> string

exception Type_error of error

val check : env:Meta.Check_env.env -> size:int -> term:Syntax.t -> tp:Domain.t -> m:mode -> unit
val synth : env:Meta.Check_env.env -> size:int -> term:Syntax.t -> m:mode -> Domain.t
val check_tp : env:Meta.Check_env.env -> size:int -> term:Syntax.t -> m:mode -> unit
