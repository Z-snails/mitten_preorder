open Mode_theory
module S = Syntax

let pp_m (fmt : Format.formatter) (m : m) = Format.fprintf fmt "%s" (mod_pp m)
let pp_syntax (fmt : Format.formatter) (t : Syntax.t) = Format.fprintf fmt "%s" (S.pp t)

type envhead =
  | Val of t Lazy.t
  | M of m
  [@@deriving show]
(* Do environments need locks? mitten paper doesn't include locks in environments.
   gratzer22 normalisation for MTT doesn't use NbE.
   In env_val locks are ignored. *)
and env = envhead list [@@deriving show]
and clos = Clos of {term : Syntax.t [@printer pp_syntax]; env : env [@opaque]} [@@deriving show]
and clos2 = Clos2 of {term : Syntax.t [@printer pp_syntax]; env : env [@opaque]} [@@deriving show]
and clos3 = Clos3 of {term : Syntax.t [@printer pp_syntax]; env : env [@opaque]} [@@deriving show]
and t =
  | Lam of m * clos
  | Neutral of { tp : t [@opaque]; term : ne }
  | Nat
  | Zero
  | Suc of t
  | Pi of m * t * clos
  | Sig of t * clos
  | Pair of t * t
  | Refl of t
  | Id of t * t * t
  | Uni of unit
  | Tymod of m * t
  | Mod of m * t
  [@@deriving show]
(* An eliminator without the scrutinee *)
and elim =
  | Ap of m * nf
  | Fst | Snd
  | NRec of { motive: clos; zero: t; suc: clos2 }
  | Letmod of { mod1: m; mod2: m; motive: clos; body: clos; argtp: t }
  | J of { motive: clos3; refl: clos; tp: t; left: t; right: t }
  [@@deriving show]
(* The head of a neutral form *)
and head =
  | Var of int (* de Bruijn level *)
    [@printer fun fmt i -> Format.fprintf fmt "lvl%d" i]
  | Axiom of string * t
    [@printer fun fmt (n, _) -> Format.fprintf fmt "%s" n]
  | Meta of S.metavar * tp_sub
  [@printer fun fmt (m, sub) -> Format.fprintf fmt "%s" (S.show_metavar m)]
  [@@deriving show]
and tp_sub = nf Lazy.t list
and sub = t Lazy.t list

(* A neutral form ie a list of eliminators applied to a neutral head *)
and ne = { head: head; spine: elim list }
  [@@deriving show]
(* and ne = *)
(*   | Var of int (* DeBruijn levels for variables *) *)
(*   | Ap of m * ne * nf *)
(*   | Fst of ne *)
(*   | Snd of ne *)
(*   | NRec of clos * t * clos2 * ne *)
(*   | Letmod of m * m * clos * clos * t * ne *)
(*   | J of clos3 * clos * t * t * t * ne *)
(*   | Axiom of string * t *)
(*   | Meta of S.metavar * nf list *)
and nf =
  | Normal of {tp : t; term : t}
  [@@deriving show]

let untp_sub = List.map (Lazy.map_val (function Normal { term } -> term))

let var (lvl : int) = { head = Var lvl; spine = [] }

let mk_var tp lev = Neutral {tp; term = var lev}

let elim (e : elim) (t : ne) : ne = { head = t.head; spine = e :: t.spine }

let axiom (name : string) (tp : t) = { head = Axiom (name, tp); spine = [] }

let meta (m : S.metavar) (sub : tp_sub) = { head = Meta (m, sub); spine = [] }

(* env_val is giving the nth entry of the environment list, ONLY counting values. env_cell then gives the corresponding
   cell as it is required for the nbe algorithm *)

let env_size env =
  let rec go e acc =
    match e with
    | [] -> acc
    | M _ :: e' -> go e' acc
    | Val _ :: e' -> go e' (acc + 1)
  in go env 0

let rec env_val env i =
  match env with
  | [] -> raise (Invalid_argument "env_val should not reach the empty list")
  | Val v :: lst ->
    if Int.equal i 0
      then Lazy.force v
      else if i > 0 then env_val lst (i - 1)
      else failwith "env_cell does not accept negative input"
  | M _ :: lst -> env_val lst i

let lvl_to_ix ~size ~lvl = size - (lvl + 1)
let ix_to_lvl ~size ~ix = size - (ix + 1)

let value t = Val (Lazy.from_val t)
