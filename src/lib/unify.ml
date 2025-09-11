module S = Syntax
module D = Domain
module MT = Mode_theory

open Meta.Check_env

type mode = MT.mode
type modality = MT.m

let pp_modality (fmt : Format.formatter) (m : modality) =
    Format.fprintf fmt "%s" (MT.mod_pp m)

(** An unelaborated and unchecked preterm *)
type preterm =
    | Var of int
    | Let of preterm * preterm
    | Check of preterm * preterm

    | Nat | Zero | Suc of preterm
    | NRec of { motive : preterm; zero : preterm; suc : preterm; scr : preterm }

    | Pi of modality * preterm * preterm
    | Lam of modality option * preterm
    | Ap of modality option * preterm * preterm

    | Sig of preterm * preterm
    | Pair of preterm * preterm
    | Fst of preterm | Snd of preterm

    | Id of preterm * preterm * preterm
    | Refl of preterm
    | J of { motive : preterm; refl : preterm; eq : preterm }

    | Uni of unit

    | TyMod of modality * preterm
    | Mod of modality * preterm
    (* letmod mod1 (motive) mod mod2(_) <- scrutinee in body  *)
    | Letmod of {
        mod1: modality; mod2: modality;
        motive: preterm;
        scrutinee: preterm;
        body: preterm;
    }

    | Hole of string option
    [@@deriving show]

(** A description of the left and right operands in an error *)
type error_desc =
    | Expected_inferred
    | Left_right

(* TODO: readback all the `Domain.t`s *)
type elab_error =
    (* Modal things *)
    | Mode_mismatch of
        { left: mode; right: mode; desc: error_desc
        ; modality: modality option; term: preterm }
    | Modality_mismatch of
        { left: modality; right: modality; desc: error_desc; term: preterm option }
    | Missing_2cell of
        { lesser: modality; greater: modality; term: preterm }
    | Cant_infer_modality of preterm

    (* Unification *)
    | While_unifying of
        { tp: Domain.t option; left: Domain.t; right: Domain.t
        ; desc: error_desc ; inner: elab_error; term: preterm }
    | Unify_error of
        { tp: Domain.t option; left: Domain.t; right: Domain.t }
    | Unify_error_elim of
        { left: Domain.elim; right: Domain.elim }


    (* Metavariable solving *)
    | While_solving of
        { meta: S.metavar; sub: Domain.nf Lazy.t list; tp: Domain.t
        ; spine: Domain.elim list; rhs: Domain.t; inner: elab_error }
    | Not_renaming of (Domain.t, Domain.elim) Either.t
    (* | Not_identity_2cell of *)
    (*     { prob_mod: modality; prob_lock: modality *)
    (*     ; meta_mod: modality; meta_lock: modality *)
    (*     ; variable: int } *)
    (* | Cant_factor_2cell of { lower_bound: modality; in_problem: modality; level: int } *)
    | Inaccessible_in_solution of { mu: modality; locks: modality; var: int }
    | Occurs_check
    | Non_linear of int
    | Escaped_var of int

    (* Metadata *)
    | While_elaborating of Concrete_syntax.ident * int * elab_error

let rec pp_error (e : elab_error) = match e with
    | Mode_mismatch e ->
        Printf.sprintf "Mode mismatch: expected mode %s, got %s in term\n%s"
            (MT.mode_pp e.left) (MT.mode_pp e.right) (show_preterm e.term)
    | Modality_mismatch e ->
        Printf.sprintf "Modality mismatch: expected modality %s, got %s%s"
            (MT.mod_pp e.left) (MT.mod_pp e.right)
            (Option.fold ~none:"" ~some:(fun x -> " in term\n" ^ show_preterm x) e.term)
    | Missing_2cell e ->
        Printf.sprintf "Missing 2-cell: expected 2-cell from %s to %s in term %s"
            (MT.mod_pp e.lesser) (MT.mod_pp e.greater) (show_preterm e.term)
    | Cant_infer_modality term ->
        Printf.sprintf "Unable to infer modality in %s" (show_preterm term)
    | Unify_error e ->
        Printf.sprintf "Unable to unify\n%s\nand\n%s"
            (Domain.show e.left) (Domain.show e.right)
    | Unify_error_elim e ->
        Printf.sprintf "Unable to unify\n%sand\n%s"
            (Domain.show_elim e.left) (Domain.show_elim e.right)
    | While_unifying e ->
        Printf.sprintf
            "While unifying expected type\n%s\nand inferred type\n%s\nof term %s\n\n%s"
            (Domain.show e.left) (Domain.show e.right)
            (show_preterm e.term) (pp_error e.inner)

    | While_solving e ->
        (* TODO: read_back before printing *)
        Printf.sprintf "While solving metavariable %s = %s\n\n%s"
            (Domain.show (Neutral
                { tp = e.tp
                ; term = { head = D.Meta (e.meta, e.sub); spine = e.spine }}))
            (Domain.show e.rhs) (pp_error e.inner)
    | Not_renaming e ->
        let tm = match e with
            | Left x -> Domain.show x
            | Right e -> Domain.show_elim e
        in
        Printf.sprintf "Unification problem is not a renaming:\n%s is not a variable" tm
    (* | Not_identity_2cell e -> *)
    (*     (* TODO: lookup variable name *) *)
    (*     Printf.sprintf *)
    (*         "Variable %d is available with modality %s and lock %s, but the metavariable expects it at modality %s and lock %s" *)
    (*         e.variable *)
    (*         (MT.mod_pp e.prob_mod) (MT.mod_pp e.prob_lock) *)
    (*         (MT.mod_pp e.meta_mod) (MT.mod_pp e.meta_lock) *)
    (* | Cant_factor_2cell e -> *)
    (*     Printf.sprintf *)
    (*         "Unable to factor modality %s of level %d in terms of lower bound %s" *)
    (*         (MT.mod_pp e.in_problem) e.level (MT.mod_pp e.lower_bound) *)
    | Inaccessible_in_solution e ->
        Printf.sprintf
            "Variable %d is not accessible in the solution: missing 2-cell %s <= %s"
            e.var (MT.mod_pp e.mu) (MT.mod_pp e.locks)
    | Occurs_check ->
        "Occurs check: Metavariable occurs in the RHS of the unification problem"
    | Non_linear v ->
        Printf.sprintf
            "Non-linear variable %d can't be pruned: since it occurs in the solution" v
    | Escaped_var v ->
        (* TODO: print variable name *)
        Printf.sprintf "Escaping variable %d is not bound in the solution" v
    | While_elaborating (n, lvl, e) ->
        Printf.sprintf "While elaborating %s (level %d)\n%s" n lvl (pp_error e)

exception Elab_error of elab_error

let elab_error (e : elab_error) = raise (Elab_error e)

let check_mod_eq
    (left : modality) (right : modality) (desc : error_desc) (term : preterm option) =
    if not (MT.eq_mod left right)
    then elab_error (Modality_mismatch { left; right; desc; term })

(* ============================================================================
   Unification
============================================================================ *)

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

let unify_error ?tp left right = elab_error (Unify_error { tp; left; right })

type pren =
    { dom_size: int
    ; cod_size: int
    ; map: (int * modality) IntMap.t
    ; non_linear: IntSet.t }

let show_pren (pren : pren) : string =
    String.concat ", " (List.map
        (fun (x, (y, _)) -> Printf.sprintf "%d |-> %d" x y)
        (IntMap.bindings pren.map))

(** Check a delayed substitution and spine are a partial renaming,
    ie a list of variables, each unlocked by the identity 2-cell.
    Everything here uses de Bruijn levels. *)
let invert
    ~prob_env:(prob_env : env) ~size:(prob_size : int) ~meta_env:(meta_env : env)
    (sub : Domain.nf Lazy.t list) (spine : Domain.elim list)
    : (pren, elab_error) result =

    let (let*) = Result.bind in
    let assert_res = fun b e -> if b then Ok () else Error e in

    (** If a value is a bound variable, then return its de Bruijn index *)
    let unwrap_var (t : Domain.t) : (modality * int, elab_error) result =
        match Nbe.force prob_size t with
        | Neutral { term = { head = Var lvl; spine = [] } } ->
            begin match nth_tm prob_env (D.lvl_to_ix ~size:prob_size ~lvl) with
                | Term { defined = false; mu } -> Ok (mu, lvl)
                | Term { defined = true } | TopLevel _ -> Error (Not_renaming (Left t))
                | M _ -> failwith "Unreachable"
            end
        | t' -> Error (Not_renaming (Left t'))
    in

    (** Add a variable to a partial renaming. If it already exists, then move
        it to the set of non-linear variables *)
    let add_var ~var ~mu acc : pren =
        if IntMap.mem var acc.map
        then
            { dom_size = acc.dom_size + 1
            ; cod_size = acc.cod_size
            ; map = IntMap.remove var acc.map
            ; non_linear = IntSet.add var acc.non_linear }
        else { acc with
            map = IntMap.add var (acc.dom_size, mu) acc.map;
            dom_size = acc.dom_size + 1 }
    in

    (** Increment dom_size to account for top-level variables *)
    let add_top_level acc = { acc with dom_size = acc.dom_size + 1 } in

    let rec go_spine
        (spine : Domain.elim list) (acc : pren) : (pren, elab_error) result =
        match spine with
        | [] -> Ok acc
        | Ap (meta_mod, Normal x) :: spine' ->
            let* (prob_mod, var) = unwrap_var x.term in
            (* let meta_lock = MT.idm in *)
            (* let prob_lock = nth_cell prob_env var in *)
            let* _ = assert_res (not @@ IntMap.mem var acc.map) (Non_linear var) in
            (* let* _ = assert_res *)
            (*     (MT.eq_mod meta_mod prob_mod && MT.eq_mod prob_lock meta_lock) *)
            (*     (Not_identity_2cell *)
            (*         { prob_mod; prob_lock; meta_mod; meta_lock; variable = var }) in *)
            go_spine spine' (add_var ~var ~mu:meta_mod acc)
        | e :: _ -> Error (Not_renaming (Right e))
    in

    let rec go_sub
        (env : env) (sub : D.tp_sub) (acc : pren): (pren, elab_error) result =
        match env, sub with
        | [], [] -> go_spine (List.rev spine) acc
        | M _ :: env', _ -> go_sub env' sub acc
        | (Term { defined = true } | TopLevel _) :: env', _ :: sub' ->
            go_sub env' sub' (add_top_level acc)
        | Term { defined = false; mu = meta_mod } :: env', lazy (Normal x) :: sub' ->
            let* (prob_mod, var) = unwrap_var x.term in
            (* let meta_lock = Meta.Check_env.locks env' in *)
            (* let prob_lock = nth_cell prob_env var in *)
            let* _ = assert_res (not @@ IntMap.mem var acc.map) (Non_linear var) in
            (* let* _ = assert_res *)
            (*     (MT.eq_mod prob_mod meta_mod && MT.eq_mod prob_lock meta_lock) *)
            (*     (Not_identity_2cell *)
            (*         { prob_mod; prob_lock; meta_mod; meta_lock; variable = var }) in *)
            go_sub env' sub' (add_var ~var ~mu:meta_mod acc)
        | _ -> failwith "Unreachable"
    in

    go_sub (List.rev meta_env) sub
        { dom_size = 0; cod_size = prob_size
        ; map = IntMap.empty; non_linear = IntSet.empty }

(** An environment that only tracks modalities, not types *)
type mod_env_head =
    | Tm of modality option
    | Lock of modality
type mod_env = mod_env_head list

type solve_ctx =
    { env: mod_env; prob_size: int; meta_size: int; rigid: bool
    ; occurs_check: S.metavar option; pren: pren option }

let lift (mu : modality option) (ctx : solve_ctx) =
    { ctx with
        env = Tm mu :: ctx.env;
        prob_size = ctx.prob_size + 1;
        meta_size = ctx.meta_size + 1;
    }
let lift_idm = lift (Some MT.idm)

let lock (mu : modality) (ctx : solve_ctx) =
    { ctx with env = Lock mu :: ctx.env }

let rec env_to_mod_env env (sp : D.elim list) = match sp, env with
    | [], [] -> []
    | Ap (mu, _) :: sp', _ -> Tm (Some mu) :: env_to_mod_env env sp'
    | _ :: _, _ -> failwith "Unreachable"
    | [], Term { mu } :: env -> Tm (Some mu) :: env_to_mod_env env sp
    | [], TopLevel _ :: env -> Tm None :: env_to_mod_env env sp
    | [], M mu :: env -> Lock mu :: env_to_mod_env env sp

let rec nth_cell (env : mod_env) (i : int) : modality option * modality =
    if i < 0 then invalid_arg "nth_lockless: negative de Bruijn index";
    match env, i with
    | [], _ -> failwith "Unreachable"
    | Tm mu :: env', 0 -> (mu, MT.idm)
    | Tm _ :: env', _ -> nth_cell env' (i - 1)
    | Lock mu :: env', _ ->
        let (nu, locks) = nth_cell env' i in
        (nu, MT.compm (locks, mu))

let check_var (ctx : solve_ctx) (ix : int) =
    let ix' = match ctx.pren with
        | Some pren ->
            let cod_lvl = D.ix_to_lvl ~size:ctx.prob_size ~ix in
            begin match IntMap.find_opt cod_lvl pren.map with
            | Some (meta_lvl, _) -> D.lvl_to_ix ~size:ctx.meta_size ~lvl:meta_lvl
            | None ->
                if cod_lvl < pren.cod_size
                then if IntSet.mem cod_lvl pren.non_linear
                        then elab_error (Non_linear cod_lvl)
                        else elab_error (Escaped_var cod_lvl)
                else ix (* not free in codomain *)
            end
        | None -> ix
    in

    let lvl = D.ix_to_lvl ~size:ctx.meta_size ~ix:ix' in
    let (mu, locks) = nth_cell ctx.env ix' in
    match mu with
    | Some mu ->
        if ctx.rigid && not (MT.leq mu locks)
            then elab_error
                (Inaccessible_in_solution { mu; locks; var = lvl })
    | None -> ()

let rec check_vars (ctx : solve_ctx) (tm : Syntax.t) =
    match tm with
    | Syntax.Var ix -> check_var ctx ix
    | Syntax.Let (tm, body) ->
        check_vars ctx tm;
        check_vars (ctx |> lift_idm) body
    | Syntax.Check (tm, tp) ->
        check_vars ctx tm; check_vars ctx tp
    | Syntax.Nat -> ()
    | Syntax.Zero -> ()
    | Syntax.Suc t -> check_vars ctx t
    | Syntax.NRec (mot, zero, suc, scr) ->
        check_vars (ctx |> lift_idm) mot;
        check_vars ctx zero;
        check_vars (ctx |> lift_idm |> lift_idm) suc;
        check_vars ctx scr
    | Syntax.Pi (mu, dom, cod) ->
        check_vars (ctx |> lock mu) dom;
        check_vars (ctx |> lift (Some mu)) cod
    | Syntax.Lam (mu, t) -> check_vars (ctx |> lift (Some mu)) t
    | Syntax.Ap (mu, f, x) ->
        check_vars ctx f;
        check_vars (ctx |> lock mu) x
    | Syntax.Sig (fst, snd) ->
        check_vars ctx fst;
        check_vars (ctx |> lift_idm) snd
    | Syntax.Pair (fst, snd) ->
        check_vars ctx fst;
        check_vars ctx snd
    | Syntax.Fst p -> check_vars ctx p
    | Syntax.Snd p -> check_vars ctx p
    | Syntax.Id (tp, x, y) ->
        check_vars ctx tp;
        check_vars ctx x;
        check_vars ctx y
    | Syntax.Refl t -> check_vars ctx t
    | Syntax.J (mot, refl, scr) ->
        check_vars (ctx |> lift_idm |> lift_idm |> lift_idm) mot;
        check_vars (ctx |> lift_idm) refl;
        check_vars ctx scr
    | Syntax.Uni _ -> ()
    | Syntax.TyMod (mu, t) -> check_vars (ctx |> lock mu) t
    | Syntax.Mod (mu, t) -> check_vars (ctx |> lock mu) t
    | Syntax.Letmod (mu, nu, mot, body, scr) ->
        check_vars (ctx |> lift_idm) mot;
        check_vars (ctx |> lift_idm) body;
        check_vars (ctx |> lock mu) scr
    (* An axiom can't possibly contain any local variables *)
    | Syntax.Axiom (ax, tp) -> ()
    | Syntax.Meta (m, sub) ->
        if Some m = ctx.occurs_check then elab_error Occurs_check;

        let entry = Meta.lookup m in
        Option.iter (fun meta -> Meta.add_used_by entry meta) ctx.occurs_check;
        let ctx' = { ctx with rigid = false } in
        check_vars_sub ctx' (List.rev entry.context) sub

and check_vars_sub (ctx : solve_ctx) (env : env) (sub : Syntax.t list) =
    match env, sub with
    | [], [] -> ()
    | TopLevel _ :: ctx', _ :: sub' -> check_vars_sub ctx ctx' sub'
    | Term { mu } :: ctx', t :: sub' ->
        (* check_vars pren (Lock mu :: env) size false t; *)
        check_vars ctx t;
        check_vars_sub ctx ctx' sub'
    | M _ :: ctx', _ -> check_vars_sub ctx ctx' sub
    | _ -> failwith "Unreachable"

(** Apply a partial renaming to a term, also checking for occurances of a given metavariable *)
let apply_pren
    ~env:(env : env) ~size:(size : int)
    ~meta:(meta : S.metavar) ~pren:(pren : pren) ~spine:(spine : D.elim list)
    ~tp:(tp : Domain.t) ~term:(term : Domain.t) : (Domain.t, elab_error) result =

    (** Convert the problem environment into a NbE environment that renames the
        variables *)
    let rec create_env env = match env with
        | [] -> []
        | TopLevel { term } :: env' -> D.value term :: create_env env'
        | Term { level; tp } :: env' ->
            let v = match IntMap.find_opt level pren.map with
            | Some (v', _) -> Lazy.from_val (D.mk_var tp v')
            | None -> lazy (failwith "Unreachable: escaped/non-linear variable")
            in D.Val v :: create_env env'
        | M mu :: env' -> M mu :: create_env env'
    in

    let entry = Meta.lookup meta in
    let tm = Nbe.read_back_nf pren.cod_size (Normal { tp; term }) in
    (* Printf.printf "while inverting, got term\n%s\n%!" (Syntax.pp tm); *)
    try
        check_vars
            { env = env_to_mod_env entry.context spine
            ; prob_size = size
            ; meta_size = entry.size + List.length spine
            ; rigid = true
            ; occurs_check = Some meta
            ; pren = Some pren }
            tm;
        Ok (Nbe.eval tm (create_env env))
    with
    | Elab_error e -> Error e

let show_val ~size ~tp ~term = Nbe.read_back_nf size (Normal { tp; term }) |> S.pp

let solve
    ~env:(env : env) ~size ~meta:(meta : S.metavar) ~sub:(sub : Domain.nf Lazy.t list)
    ~spine:(spine : Domain.elim list) ~rhs:(rhs : Domain.t) ~tp:(tp : Domain.t)
    ~mode:(mode : mode) : unit =

    (** Wrap an inner error with some context *)
    let err inner = While_solving { meta; sub; spine; rhs; inner; tp } in
    let unwrap : type a. (a, elab_error) result -> a = function
        | Ok x -> x
        | Error e -> elab_error (err e)
    in

    (* Printf.printf "Got unification problem\n%s\n=\n%s\n\n%!" *)
    (*     (show_val ~size ~tp *)
    (*         ~term:(D.Neutral { tp; term = { head = D.Meta (meta, sub); spine } })) *)
    (*     (show_val ~size ~tp ~term:rhs); *)

    let rec lams (spine : Domain.elim list) (term : Syntax.t) =
        match spine with
        | [] -> term
        | D.Ap (mu, _) :: spine' -> lams spine' (Lam (mu, term))
        | _ -> failwith "Unreachable"
    in

    let rec get_env
        (env : env) (size : int) (spine : Domain.elim list)
        (tp : Domain.t) : int * Domain.t =
        match spine, Nbe.force size tp with
        | [], tp -> (size, tp)
        | _ :: spine', Pi (mu, dom, cod) ->
            let (var, new_env) = add_var ~size ~mode ~mu ~tp:dom env in
            get_env new_env (size + 1) spine' (Nbe.do_clos' cod var)
        | _ -> failwith "Expected Pi type in Elab.solve/get_env"
    in

    let entry = Meta.lookup meta in
    let pren =
        unwrap @@ invert ~prob_env:env ~size ~meta_env:entry.context sub spine in

    let (inner_size, inner_tp) =
        get_env entry.context entry.size spine entry.sem_tp in
    (* TODO: check inner_tp is well-formed after pruning non-linear variables *)
    (* TODO: check each type in the context is well-formed after pruning
       non-linear variables *)

    (* The solution without lambdas applied *)
    let inner_sol = unwrap @@
        apply_pren ~env ~size ~meta ~pren ~spine ~tp ~term:rhs in
    let inner =
        Nbe.read_back_nf inner_size (Normal { tp = inner_tp; term = inner_sol }) in

    (* Printf.printf "  Got inner solution %s\n" (Syntax.pp inner); *)

    (* Now add lambdas *)
    let sol = lams spine inner in
    Printf.printf "Solved %s as %s\n\n%!" (S.show_metavar meta) (S.pp sol);

    List.iter (fun m ->
        Printf.printf "While solving %s, checking solution to %s is correct\n%!"
            (S.show_metavar meta) (S.show_metavar m);
        let entry = Meta.lookup m in
        let tm = Option.get entry.value in
        let tm' = Meta.remove_solved entry.context tm in
        try
            check_vars
                { prob_size = entry.size
                ; meta_size = entry.size
                ; env = env_to_mod_env entry.context []
                ; rigid = true
                ; pren = None
                ; occurs_check = None}
                tm';
            entry.value <- Some tm'
        with
        | Elab_error e -> raise (Elab_error (err e))
    ) (Meta.used_by entry);

    Meta.solve meta sol

let rec unify
    ~env:(env : env) ~size:(size : int) ~tp:(tp : Domain.t) ~mode:(mode : mode)
    (left : Domain.t) (right : Domain.t) =
    match Nbe.force size tp, Nbe.force size left, Nbe.force size right with
    (* Pi types *)
    | Pi (mu, dom, cod), left', right' ->
        let (var, new_env) = add_var ~size ~mode ~mu ~tp:dom env in
        let sem_cod = Nbe.do_clos' cod var in
        let sem_left = Nbe.do_ap left' (Lazy.from_val var) in
        let sem_right = Nbe.do_ap right' (Lazy.from_val var) in
        unify ~env:new_env ~size:(size + 1) ~tp:sem_cod ~mode sem_left sem_right

    | _, Pi (mu1, dom1, cod1), Pi (mu2, dom2, cod2) ->
        check_mod_eq mu1 mu2 Left_right None;
        unify ~env:(M mu1 :: env) ~size ~tp ~mode dom1 dom2;
        let (var, new_env) = add_var ~size ~mode ~mu:mu1 ~tp:dom1 env in
        let sem_cod1 = Nbe.do_clos' cod1 var and sem_cod2 = Nbe.do_clos' cod2 var in
        unify ~env:new_env ~size ~tp ~mode sem_cod1 sem_cod2

    (* Universe *)
    | _, Uni l1, Uni l2 -> ()
        (* TODO: universe levels *)
        (* if l1 <> l2 then unify_error ~tp left right *)

    (* Nat *)
    | _, Nat, Nat -> ()
    | _, Zero, Zero -> ()
    | _, Suc x, Suc y ->
        unify ~env ~size ~tp:Nat ~mode x y

    (* Metavariables *)
    | _
    , (Neutral { term = { head = Meta (m1, sub1) } as left_ne  } as left)
    , (Neutral { term = { head = Meta (m2, sub2) } as right_ne } as right) ->
        if m1 = m2
        then unify_ne ~env ~size ~mode ~tp left_ne right_ne
        else begin
            try
                solve ~env ~size ~meta:m1 ~sub:sub1 ~spine:left_ne.spine
                    ~rhs:right ~mode ~tp
            with
            | Elab_error (While_solving _) ->
                solve ~env ~size ~meta:m2 ~sub:sub2 ~spine:right_ne.spine
                    ~rhs:left ~mode ~tp
        end

    | _, Neutral { term = { head = Meta (meta, sub); spine } }, rhs ->
        solve ~env ~size ~meta ~sub ~spine ~rhs ~mode ~tp
    | _, rhs, Neutral { term = { head = Meta (meta, sub); spine } } ->
        solve ~env ~size ~meta ~sub ~spine ~rhs ~mode ~tp

    (* Non-meta neutrals *)
    | _, Neutral x, Neutral y ->
        unify_ne ~env ~size ~mode ~tp:tp x.term y.term

    (* Id *)
    | _, Id (tp1, x1, y1), Id (tp2, x2, y2) ->
        unify ~env ~size ~mode ~tp tp1 tp2;
        unify ~env ~size ~mode ~tp:tp1 x1 x2;
        unify ~env ~size ~mode ~tp:tp1 y1 y2;

    | Id (tp, _, _), Refl x, Refl y ->
        unify ~env ~size ~mode ~tp x y

    (* Tymod *)
    | _, Tymod (mu1, t1), Tymod (mu2, t2) ->
        check_mod_eq mu1 mu2 Left_right None;
        (* if not @@ MT.eq_mod mu1 mu2 then *)
        (*     elab_error (Modality_mismatch *)
        (*         { left = mu1; right = mu2; desc = Left_right; term = None }); *)
        unify ~env:(M mu1 :: env) ~size ~mode:(MT.dom_mod mu1 mode) ~tp:tp t1 t2

    | Tymod (mu, arg_tp), Mod (_, x), Mod (_, y) ->
        (* Printf.printf "unify at Tymod\n%!"; *)
        unify ~env:(M mu :: env) ~size ~mode:(MT.dom_mod mu mode) ~tp:arg_tp x y
    (* TODO: eta law for Tymod? *)

    (* Sigma *)
    | _, Sig (fst1, snd1), Sig (fst2, snd2) ->
        unify ~env ~size ~mode ~tp fst1 fst2;
        let (fst_var, new_env) = add_var ~size ~mode ~mu:MT.idm ~tp:fst1 env in
        let snd1 = Nbe.do_clos' snd1 fst_var and snd2 = Nbe.do_clos' snd2 fst_var in
        unify ~env:new_env ~size:(size + 1) ~mode ~tp snd1 snd2;

    | Sig (fst_tp, snd_clos), x, y ->
        let fst_x = Nbe.do_fst x and fst_y = Nbe.do_fst y in
        unify ~env ~size ~mode ~tp:fst_tp fst_x fst_y;
        let snd_tp = Nbe.do_clos' snd_clos fst_x in
        unify ~env ~size ~mode ~tp:snd_tp (Nbe.do_snd x) (Nbe.do_snd y)

    | tp, x, y ->
        Printf.printf "unify other case\n%s\nand\n%s\nat\n%s\n"
            (Domain.show x) (Domain.show y) (Domain.show tp);
        elab_error (Unify_error { left = x; right = y; tp = Some tp })

and unify_nf
    ~env:(env : env) ~size:(size : int) ~mode:(mode : mode)
    (Normal left : Domain.nf) (Normal right : Domain.nf) =
    unify ~env ~size ~mode ~tp:(left.tp) left.term right.term

and unify_elim
    ~env:(env : env) ~size:(size : int) ~mode:(mode : mode)
    (left : Domain.elim) (right : Domain.elim) =
    match left, right with
    | Ap (mu, x), Ap (nu, y) ->
        assert (MT.eq_mod mu nu);
        unify_nf ~env ~size ~mode x y

    | Fst, Fst -> ()
    | Snd, Snd -> ()

    | NRec x, NRec y -> S.todo "unify NRec"

    | Letmod x, Letmod y ->
        (* Printf.printf "x.mod1 = %s, x.mod2 = %s, y.mod1 = %s, y.mod2 = %s\n%!" *)
        (*     (MT.mod_pp x.mod1) (MT.mod_pp x.mod2) (MT.mod_pp y.mod1) (MT.mod_pp y.mod2); *)
        check_mod_eq x.mod1 y.mod1 Left_right None;
        check_mod_eq x.mod2 y.mod2 Left_right None;
        let mod12 = MT.compm (x.mod1, x.mod2) in
        unify_tp ~env:(M mod12 :: env) ~size ~mode x.argtp y.argtp;
        let (mot_var, mot_env) =
            add_var ~size ~mode ~mu:x.mod1 ~tp:(D.Tymod (x.mod2, x.argtp)) env in
        let mot_x = Nbe.do_clos' x.motive mot_var in
        let mot_y = Nbe.do_clos' y.motive mot_var in
        unify_tp ~env:mot_env ~size:(size + 1) ~mode mot_x mot_y;
        let (body_var, body_env) =
            add_var ~size ~mode ~mu:mod12 ~tp:x.argtp env in
        let body_tp = Nbe.do_clos' x.motive (D.Mod (x.mod2, body_var)) in
        let body_x = Nbe.do_clos' x.body body_var in
        let body_y = Nbe.do_clos' y.body body_var in
        (* () *)
        (* Printf.printf "About to unify\n%s\nand\n%s\n" (Domain.show body_x) (Domain.show body_y); *)
        (* let pp_clos (D.Clos { term }) = Syntax.pp term in *)
        (* Printf.printf "x.body = %s\ny.body = %s\n" (pp_clos x.body) (pp_clos y.body); *)
        unify ~env:body_env ~size:(size + 1) ~tp:body_tp ~mode body_x body_y

    | J x, J y ->
        unify_tp ~env ~size ~mode x.tp y.tp;

        let (mot_var1, mot_env) =
            add_var ~size ~mode ~mu:MT.idm ~tp:x.tp env in
        let (mot_var2, mot_env) =
            add_var ~size:(size + 1) ~mode ~mu:MT.idm ~tp:x.tp mot_env in
        let (mot_var3, mot_env) =
            add_var ~size:(size + 2) ~mode ~mu:MT.idm
                ~tp:(D.Id (x.tp, mot_var1, mot_var2)) mot_env in
        unify_tp ~env:mot_env ~size:(size + 3) ~mode
            (Nbe.do_clos3' x.motive mot_var1 mot_var2 mot_var3)
            (Nbe.do_clos3' y.motive mot_var1 mot_var2 mot_var3);

        let (refl_var, refl_env) =
            add_var ~size ~mode ~mu:MT.idm ~tp:x.tp env in
        let refl_tp = Nbe.do_clos3' x.motive refl_var refl_var (D.Refl refl_var) in
        unify ~env:refl_env ~size:(size + 1) ~tp:refl_tp ~mode
            (Nbe.do_clos' x.refl refl_var) (Nbe.do_clos' y.refl refl_var)

    | _, _ -> elab_error (Unify_error_elim { left; right })

and unify_sp
    ~env:(env : env) ~size:(size : int) ~mode:(mode : mode)
    (left : Domain.elim list) (right : Domain.elim list) =
    match left, right with
    | [], [] -> ()
    | (x :: xs), (y :: ys) ->
        unify_elim ~env ~size ~mode x y;
        let new_mode = match x with
            | Letmod x -> MT.dom_mod x.mod1 mode
            | _ -> mode
        in
        unify_sp ~env ~size ~mode:new_mode xs ys
    | _, _ -> ()

(** Unify neutral values by unifying their heads and spines.
    This does not solve metavariables *)
and unify_ne
    ~env:(env : env) ~size:(size : int) ~mode:(mode : mode)
    ~tp:(tp : Domain.t) (left : Domain.ne) (right : Domain.ne) =
    match left.head, right.head with
    | Var x, Var y when x = y ->
        unify_sp ~env ~size ~mode left.spine right.spine

    | Axiom (n, _), Axiom (m, _) when n = m ->
        unify_sp ~env ~size ~mode left.spine right.spine

    | Meta (m1, sub1), Meta (m2, sub2) when m1 = m2 ->
        unify_sp ~env ~size ~mode left.spine right.spine;
        unify_sub ~env ~size ~mode ~meta:m1 sub1 sub2

    (* TODO: only print the mismatching section, rather than entire spine *)
    | _ -> unify_error (Neutral { tp; term = left }) (Neutral { tp; term = right })

and unify_sub
    ~env:(env : env) ~size:(size : int) ~mode:(mode : mode) ~meta:(meta : S.metavar)
    (left : Domain.tp_sub) (right : Domain.tp_sub) =

    let rec go
        (ctx : Meta.Check_env.env) (left : Domain.tp_sub) (right : Domain.tp_sub) =
        match ctx, left, right with
        | [], [], [] -> ()
        | M _ :: ctx', _, _ -> go ctx' left right
        | TopLevel _ :: ctx', _ :: left', _ :: right' ->
            go ctx' left' right'
        | Term { md; mu } :: ctx'
        , lazy (D.Normal { tp; term = x }) :: left'
        , lazy (D.Normal { term = y }) :: right' ->
            unify ~env:(M mu :: env) ~size ~tp ~mode:md x y;
            go ctx' left' right'
        | _ -> failwith "Unreachable"
    in
    let entry = Meta.lookup meta in
    go (List.rev entry.context) left right

and unify_tp
    ~env:(env : env) ~size:(size : int) ~mode:(mode : mode)
    (left : Domain.t) (right : Domain.t) =
    unify ~env ~size ~mode ~tp:(D.Uni ()) left right

let unify_catch
    ?tp:(tp : Domain.t option) ~size:(size : int) ~term:(term : preterm)
    (left : Domain.t) (right : Domain.t) (desc : error_desc)
    (f : Domain.t -> Domain.t -> 'a) : 'a =
    let left = Nbe.force size left and right = Nbe.force size right in
    try f left right with
    | Elab_error inner -> elab_error
        (While_unifying { tp; left; right; desc; inner; term })
