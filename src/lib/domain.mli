open Mode_theory

type envhead =
  | Val of t Lazy.t
  | M of m
and env = envhead list
and clos = Clos of {term : Syntax.t; env : env}
and clos2 = Clos2 of {term : Syntax.t; env : env}
and clos3 = Clos3 of {term : Syntax.t; env : env}
and t =
  | Lam of m * clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of m * t * clos
  | Sig of t * clos
  | Pair of t * t
  | Refl of t
  | Id of t * t * t
  | Uni of Syntax.uni_level
  | Tymod of m * t
  | Mod of m * t
(* An eliminator without the scrutinee *)
and elim =
  | Ap of m * nf
  | Fst | Snd
  | NRec of { motive: clos; zero: t; suc: clos2 }
  | Letmod of { mod1: m; mod2: m; motive: clos; body: clos; argtp: t }
  | J of { motive: clos3; refl: clos; tp: t; left: t; right: t }
(* The head of a neutral form *)
and head =
  | Var of int (* de Bruijn level *)
  | Axiom of string * t
  | Meta of Syntax.metavar * nf Lazy.t list
and tp_sub = nf Lazy.t list
and sub = t Lazy.t list

(* A neutral form ie a list of eliminators applied to a neutral head *)
and ne = { head: head; spine: elim list }

(* and ne = *)
(*   | Var of int (* DeBruijn levels for variables *) *)
(*   | Ap of m * ne * nf *)
(*   | Fst of ne *)
(*   | Snd of ne *)
(*   | NRec of clos * t * clos2 * ne *)
(*   | Letmod of m * m * clos * clos * t * ne *)
(*   | J of clos3 * clos * t * t * t * ne *)
(*   | Axiom of string * t *)
(*   | Meta of Syntax.metavar * nf list *)
and nf =
  | Normal of {tp : t; term : t}

val show : t -> string
val show_elim : elim -> string
val pp : Format.formatter -> t -> unit

val env_val : env -> int -> t

val mk_var : t -> int -> t

val elim : elim -> ne -> ne

val axiom : string -> t -> ne

val meta : Syntax.metavar -> tp_sub -> ne

val untp_sub : tp_sub -> sub

val lvl_to_ix : size:int -> lvl:int -> int
