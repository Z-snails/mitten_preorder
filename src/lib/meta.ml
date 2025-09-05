module S = Syntax
module D = Domain
open Mode_theory

(* TODO: find a better place for this? *)
module Check_env = struct
    (* The mode is the domain of the modality mu. This is needed because the implementation of modalities is ambiguous for identity modalitities.*)
    type env_entry =
        | Term of { term: D.t; mu: m; tp: D.t; md: mode; defined: bool }
        | TopLevel of
            { name: Concrete_syntax.ident; level: int; term: D.t; tp: D.t; md: mode }
        | M of m

    type env = env_entry list

    (** Add a term to an environment. To add a bound variable, use add_var *)
    let add_term ~md ~term ~mu ~tp ?(defined = false) env =
        Term { term; mu; tp; md; defined } :: env

    (** Add a bound variable to an environment *)
    let add_var ~size ~mode ~mu ~tp env =
        let var = D.mk_var tp size in
        (var, Term { term = var; mu; tp;
            md = dom_mod mu mode; defined = false } :: env)

    let rec nth_lockless (env : env) (i : int) : env_entry * m =
        if i < 0 then invalid_arg "nth_lockless: negative de Bruijn index";
        match env with
        | [] -> invalid_arg "nth_lockless: out of range de Bruijn index"
        | (Term _ | TopLevel _) as t :: env' ->
            if i == 0 then (t, idm) else nth_lockless env' (i - 1)
        | M mu :: env' ->
            let (tm, nu) = (nth_lockless env' i) in
            (tm, compm (nu, mu))

    let nth_tm (env : env) (i : int) : env_entry = fst (nth_lockless env i)
    let nth_cell (env : env) (i : int) : m = snd (nth_lockless env i)

    let get_var (env : env) (i : int) : m option * Domain.t * mode * m =
        match nth_lockless env i with
        | Term { mu; tp; md }, locks -> (Some mu, tp, md, locks)
        | TopLevel { tp; md }, locks -> (None, tp, md, locks)
        | _ -> failwith "nth_tm should never return a lock"

    let env_to_sem_env : env -> Domain.env =
        List.map
            (function
            | TopLevel {term; _} -> D.Val (Lazy.from_val term)
            | Term {term; mu = _; tp = _} -> D.Val (Lazy.from_val term)
            | M mu -> D.M mu)
end

open Check_env

module MetaMap = Map.Make(Int)
type 'a map = 'a MetaMap.t
module MetaSet = Set.Make(Int)

type entry = {
    name: string;
    context: env;
    size: int;
    sem_tp: Domain.t;
    tp: Syntax.t;
    mutable value: (Domain.t * Syntax.t) option;
    mutable used_by: MetaSet.t (* TODO: use this (see README.md) *)
}

let next_meta : int ref = ref 1
(* Ideally should be a dynamically sized array *)
let store : entry map ref = ref MetaMap.empty

let create (mk : int -> entry) : S.metavar =
    let x = !next_meta in
    incr next_meta;
    let entry = mk x in
    store := MetaMap.add x entry !store;
    S.Metavar (x, entry.name)

let vars (env : env) : Syntax.t list =
    let rec go (env : env) : Syntax.t list * int =
        match env with
        | [] -> ([], 0)
        | (Term _ | TopLevel _) :: env' ->
            let (sp, len) = go env' in
            (Var len :: sp, len + 1)
        (* | Term { defined = false } :: env' -> *)
        (*     let (sp, len) = go env' in *)
        (*     (Var len :: sp, len + 1) *)
        | M _ :: env' -> go env'
    in fst (go env)

let fresh_meta
    ?name:(name : string option) (env : env) (size : int)
    (tp : Syntax.t) (sem_tp : Domain.t) : Syntax.t =
    let m = create (fun m ->
        let n = Option.value name ~default:(string_of_int m) in
        { name = n; context = env; size; tp; sem_tp
        ; value = None; used_by = MetaSet.empty }) in
    Meta (m, vars env)

let fresh_meta_tp ?name:(name : string option) (env : env) (size : int) : Syntax.t =
    fresh_meta ?name env size (Uni ()) (Uni ())

let lookup (S.Metavar (m, _)) : entry =
    MetaMap.find m !store

let solve (m : S.metavar) (value : Domain.t) (tm : Syntax.t) : unit =
    let e = lookup m in
    assert (Option.is_none e.value);
    e.value <- Some (value, tm)

let all_metas () : (S.metavar * entry) list =
    List.map (function (m, e) -> (S.Metavar (m, e.name), e)) (MetaMap.bindings !store)

(* This is kinda pointless anyway since metavariables can be solved by later
   defintions, so we still need force all over the place. I'll use it anyway
   for printing terms *)

type sub_env =
    { root: Syntax.t list
    ; weakens: int }

let weaken_n (e : sub_env) (n : int) = { e with weakens = e.weakens + n }
let weaken (e : sub_env) = weaken_n e 1

(** Weaken a term: every free variable of tm is increased by amount *)
let weaken_tm ~amount:(amount : int) (tm : Syntax.t) : Syntax.t =
    let rec go (c : int) (tm : Syntax.t) : Syntax.t =
        match (tm : Syntax.t) with
        | S.Var v -> if v >= c then S.Var (v + amount) else S.Var v
        | S.Let (tm, body) -> S.Let (go c tm, go (c + 1) body)
        | S.Check (tm, tp) -> S.Check (go c tm, go c tp)
        | S.Nat -> S.Nat
        | S.Zero -> S.Zero
        | S.Suc t -> S.Suc (go c t)
        | S.NRec (motive, zero, suc, n) ->
            S.NRec (go (c + 1) motive, go c zero, go (c + 1) suc, go c n)
        | S.Pi (mu, dom, cod) -> S.Pi (mu, go c dom, go (c + 1) cod)
        | S.Lam t -> S.Lam (go (c + 1) t)
        | S.Ap (mu, f, x) -> S.Ap (mu, go c f, go c x)
        | S.Sig (l, r) -> S.Sig (go c l, go (c + 1) r)
        | S.Pair (l, r) -> S.Pair (go c l, go c r)
        | S.Fst t -> S.Fst (go c t)
        | S.Snd t -> S.Snd (go c t)
        | S.Id (tp, x, y) -> S.Id (go c tp, go c x, go c y)
        | S.Refl x -> S.Refl (go c x)
        | S.J (motive, refl, eq) -> S.J (go (c + 3) motive, go (c + 1) refl, go c eq)
        | S.Uni l -> S.Uni l
        | S.TyMod (mu, t) -> S.TyMod (mu, go c t)
        | S.Mod (mu, x) -> S.Mod (mu, go c x)
        | S.Letmod (mod1, mod2, motive, body, scr) ->
            S.Letmod (mod1, mod2, go (c + 1) motive, go (c + 1) body, go c scr)
        | S.Axiom (n, tp) -> S.Axiom (n, go c tp)
        | S.Meta (m, sub) -> S.Meta (m, List.map (go c) sub)
    in go 0 tm

let find (e : sub_env) (v : int) : Syntax.t =
    if v < e.weakens
    then Syntax.Var v (* A local variable, so don't adjust *)
    else weaken_tm ~amount:e.weakens (List.nth e.root (v - e.weakens))

(** Remove all solved metavariables from a term *)
let remove_solved (env : env) (t : Syntax.t) : Syntax.t =
    let rec go (env : sub_env) (t : Syntax.t) : Syntax.t =
        match t with
        | S.Var v -> find env v
        | S.Let (tm, body) -> S.Let (go env tm, go (weaken env) body)
        | S.Check (tm, tp) -> S.Check (go env tm, go env tp)
        | S.Nat -> Syntax.Nat
        | S.Zero -> Syntax.Zero
        | S.Suc t -> Syntax.Suc (go env t)
        | S.NRec (motive, zero, suc, n) ->
            S.NRec (go (weaken env) motive, go env zero, go (weaken_n env 2) suc, go env n)
        | S.Pi (mu, dom, cod) -> S.Pi (mu, go env dom, go (weaken env) cod)
        | S.Lam t -> S.Lam (go (weaken env) t)
        | S.Ap (mu, f, x) -> S.Ap (mu, go env f, go env x)
        | S.Sig (l, r) -> S.Sig (go env l, go (weaken env) r)
        | S.Pair (l, r) -> S.Pair (go env l, go env r)
        | S.Fst t -> S.Fst (go env t)
        | S.Snd t -> S.Snd (go env t)
        | S.Id (tp, x, y) -> S.Id (go env tp, go env x, go env y)
        | S.Refl x -> S.Refl (go env x)
        | S.J (motive, refl, eq) ->
            S.J (go (weaken_n env 3) motive, go (weaken env) refl, go env eq)
        | S.Uni l -> S.Uni l
        | S.TyMod (mu, x) -> S.TyMod (mu, go env x)
        | S.Mod (mu, y) -> S.Mod (mu, go env y)
        | S.Letmod (mod1, mod2, motive, body, tm) ->
            S.Letmod
                ( mod1, mod2, go (weaken env) motive
                , go (weaken env) body, go env tm)
        | S.Axiom (n, tp) -> S.Axiom (n, go env tp)
        | S.Meta (m, sub) ->
            (* Printf.printf "remove_solved/Meta %s\n%!" (S.show_metavar m); *)
            (* Printf.printf "%s\n%!" (String.concat "\n" (List.map Syntax.pp sub)); *)
            (* ignore @@ List.map (fun t -> *)
            (*     try go env t with e -> Printf.printf "  failed in term %s\n%!" (S.pp t); raise e) sub; *)
            let entry = lookup m in
            let res = match entry.value with
                | Some (_, v) -> go env (subst sub v)
                | None -> S.Meta (m, List.map (go env) sub)
            in
            (* Printf.printf "  remove_soved %s solved to\n%s\n%!" (S.show_metavar m) (S.pp res); *)
            res

    and subst (sub : Syntax.t list) (t : Syntax.t) : Syntax.t =
        go { root = List.rev sub; weakens = 0 } t

    in
    let root =
        List.mapi (fun i _ -> S.Var i)
            (List.filter (function
                | Term _ | TopLevel _ -> true
                | M _ -> false) env) in
    go { root; weakens = 0 } t
