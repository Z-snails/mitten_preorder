module S = Syntax
module D = Domain
module MT = Mode_theory

open Meta.Check_env

type mode = MT.mode
type modality = MT.m

let pp_modality (fmt : Format.formatter) (m : modality) = Format.fprintf fmt "%s" (MT.mod_pp m)

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
    | Not_identity_2cell of { in_problem: modality; in_meta: modality; variable: int }
    | Occurs_check
    | Non_linear of int
    | Escaped_var of int

    (* Metadata *)
    | While_elaborating of Concrete_syntax.ident * elab_error

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
    | Not_identity_2cell e ->
        (* TODO: lookup variable name *)
        Printf.sprintf "Variable %d is available with modality %s, but the metavariable expects it at modality %s"
            e.variable (MT.mod_pp e.in_problem) (MT.mod_pp e.in_meta)
    | Occurs_check -> "Occurs check: Metavariable occurs in the RHS of the unification problem"
    | Non_linear v -> Printf.sprintf "Unification problem is non-linear: variable %d occurs more than once" v
    | Escaped_var v ->
        (* TODO: print variable name *)
        Printf.sprintf "Escaping variable %d would not be bound in the solution" v
    | While_elaborating (n, e) ->
        Printf.sprintf "While elaborating %s\n%s" n (pp_error e)

exception Elab_error of elab_error

let while_elaborating (n : Concrete_syntax.ident) (f : unit -> 'a) : 'a =
    try
        f ()
    with
    | Elab_error e -> raise (Elab_error (While_elaborating (n, e)))

let elab_error (e : elab_error) = raise (Elab_error e)

(* DEBUG *)

let print_env (env : env_entry) =
    match env with
    | Term { mu } -> Printf.printf "Term at modality %s\n" (MT.mod_pp mu)
    | TopLevel _ -> Printf.printf "Top level\n"
    | M mu -> Printf.printf "lock %s\n" (MT.mod_pp mu)

(* ============================================================================
   Unification
============================================================================ *)

let check_mode (left : mode) (right : mode) (desc : error_desc) ?modality term =
    if not (MT.eq_mode left right)
    then elab_error (Mode_mismatch { left; right; desc; modality; term })

let check_cell (lesser : modality) (greater : modality) (term : preterm) =
    if not (MT.leq lesser greater)
    then elab_error (Missing_2cell { lesser; greater; term })

let check_mod_eq (left : modality) (right : modality) (desc : error_desc) (term : preterm option) =
    if not (MT.eq_mod left right)
    then elab_error (Modality_mismatch { left; right; desc; term })

module IntMap = Map.Make(Int)

let unify_error ?tp left right = elab_error (Unify_error { tp; left; right })

type pren = int IntMap.t

let show_pren (pren : pren) : string =
    List.fold_left
        (fun acc (x, y) -> Printf.sprintf "%s, %d |-> %d" acc x y)
        "" (IntMap.bindings pren)

(** Check a delayed substitution and spine are a partial renaming,
    ie a list of variables, each unlocked by the identity 2-cell.
    Everything here uses de Bruijn levels. *)
let invert
    ~prob_env:(prob_env : env) ~size:(size : int) ~meta_env:(meta_env : env)
    (sub : Domain.nf Lazy.t list) (spine : Domain.elim list)
    : (pren, elab_error) result =

    let (let*) = Result.bind in
    let assert_res = fun b e -> if b then Ok () else Error e in

    let get_var (t : Domain.t) : (int, elab_error) result =
        match Nbe.force size t with
        | Neutral { term = { head = Var i; spine = [] } } -> Ok i
        | t' -> Error (Not_renaming (Left t'))
    in

    let get_prob_mod (lvl : int) =
        match nth_tm prob_env (D.lvl_to_ix ~size ~lvl) with
        | Term { mu; defined = false } -> Ok mu
        | TopLevel { tp } | Term { tp; defined = true } ->
            Error (Not_renaming (Left (D.mk_var tp lvl)))
        | _ -> failwith "Unreachable"
    in

    let rec go_spine
        (spine : Domain.elim list) (size : int)
        (acc : pren) : (pren, elab_error) result =
        match spine with
        | [] -> Ok acc
        | Ap (mu, Normal x) :: spine' ->
            let* v = get_var x.term in
            let* nu = get_prob_mod v in
            let* _ = assert_res (not @@ IntMap.mem v acc) (Non_linear (v)) in
            let* _ = assert_res (MT.eq_mod mu nu) (Not_identity_2cell
                { in_problem = nu; in_meta = mu; variable = v }) in
            go_spine spine' (size + 1) (IntMap.add v size acc)
        | e :: _ -> Error (Not_renaming (Right e))
    in

    let rec go_sub
        (env : env) (sub : D.tp_sub) (size : int)
        (acc : pren): (pren, elab_error) result =
        match env, sub with
        | [], [] -> go_spine (List.rev spine) size acc
        | M _ :: env', _ -> go_sub env' sub size acc
        | (Term { defined = true } | TopLevel _) :: env', _ :: sub' ->
            go_sub env' sub' (size + 1) acc
        | Term { defined = false; mu = meta_mod } :: env', lazy (Normal x) :: sub' ->
            let* v = get_var x.term in
            let* prob_mod = get_prob_mod v in
            (* Printf.printf "prob_mod = %s for variable %d\n" (MT.mod_pp prob_mod) v; *)
            let* _ =
                assert_res (MT.eq_mod prob_mod meta_mod)
                    (Not_identity_2cell
                        { in_problem = prob_mod; in_meta = meta_mod; variable = v }) in
            let* _ = assert_res (not @@ IntMap.mem v acc) (Non_linear v) in
            go_sub env' sub' (size + 1) (IntMap.add v size acc)
        | _ -> failwith "Unreachable"
    in

    (* Printf.printf "problem env:\n"; *)
    (* List.iter print_env prob_env; *)
    (* Printf.printf "\nmeta env:\n"; *)
    (* List.iter print_env meta_env; *)

    go_sub (List.rev meta_env) sub 0 IntMap.empty

(** Apply a partial renaming to a term, also checking for occurances of a given metavariable  *)
(* TODO: replace this with read_back |> eval? *)
let apply_pren
    (pren : int IntMap.t) (term : Domain.t)
    (meta : S.metavar) : (Domain.t, elab_error) result =
    let rec go (term : Domain.t) : Domain.t =
            match term with
            | Lam t -> Lam (go_clos t)
            | Neutral { tp; term } -> Neutral { tp = go tp; term = go_ne term}
            | Nat -> Nat
            | Zero -> Zero
            | Suc t -> Suc (go t)
            | Pi (mu, dom, cod) -> Pi (mu, go dom, go_clos cod)
            | Sig (l, r) -> Sig (go l, go_clos r)
            | Pair (l, r) -> Pair (go l, go r)
            | Refl t -> Refl (go t)
            | Id (t, x, y) -> Id (go t, go x, go y)
            | Uni u -> Uni u
            | Tymod (mu, t) -> Tymod (mu, go t)
            | Mod (mu, t) -> Mod (mu, go t)

    and go_envhead (h : D.envhead) : D.envhead =
        match (h : D.envhead) with
        | D.Val t -> D.Val (Lazy.map go t)
        | D.M mu -> D.M mu

    and go_clos (Clos clos : Domain.clos) =
        D.Clos { term = clos.term; env = List.map go_envhead clos.env }

    and go_clos2 (Clos2 clos : Domain.clos2) =
        D.Clos2 { term = clos.term; env = List.map go_envhead clos.env }

    and go_clos3 (Clos3 clos : Domain.clos3) =
        D.Clos3 { term = clos.term; env = List.map go_envhead clos.env }

    and go_ne (ne : Domain.ne) =
        { head = go_head ne.head; spine = List.map go_elim ne.spine }

    and go_head (head : Domain.head) =
        match head with
        | Var v ->
            begin match IntMap.find_opt v pren with
            | Some v' -> Var v'
            | None -> elab_error (Escaped_var v)
            end
        | Axiom _ -> head
        | Meta (m, sub) ->
            if meta = m
            then elab_error Occurs_check
            else D.Meta (m, List.map (Lazy.map go_nf) sub)

    and go_nf (Normal nf) = Normal { tp = go nf.tp; term = go nf.term }

    and go_elim (elim : Domain.elim) =
        match elim with
        | D.Ap (mu, x) -> D.Ap (mu, go_nf x)
        | D.Fst -> D.Fst
        | D.Snd -> D.Snd
        | D.NRec r ->
            D.NRec { motive = go_clos r.motive; zero = go r.zero; suc = go_clos2 r.suc }
        | D.Letmod lm ->
            D.Letmod
                { mod1 = lm.mod1; mod2 = lm.mod2; motive = go_clos lm.motive
                ; body = go_clos lm.motive; argtp = go lm.argtp }
        | D.J j ->
            D.J { motive = go_clos3 j.motive; refl = go_clos j.refl
                ; tp = go j.tp; left = go j.left; right = go j.right }

    in try
        Ok (go term)
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

    Printf.printf "Got unification problem\n%s\n=\n%s\n\n%!"
        (show_val ~size ~tp
            ~term:(D.Neutral { tp; term = { head = D.Meta (meta, sub); spine } }))
        (show_val ~size ~tp ~term:rhs);

    (* List.iter (function lazy (D.Normal { term }) -> Printf.printf "%s\n%!" (Domain.show term)) sub; *)
    (* Printf.printf "\n%!"; *)

    let rec lams (spine : Domain.elim list) (term : Syntax.t) =
        match spine with
        | [] -> term
        | _ :: spine' -> lams spine' (Lam term)
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
    let pren = unwrap @@ invert ~prob_env:env ~size ~meta_env:entry.context sub spine in

    (* The solution without lambdas applied *)
    let inner_sol = unwrap @@ apply_pren pren rhs meta in
    let (inner_size, inner_tp) =
        get_env entry.context entry.size spine entry.sem_tp in
    let inner =
        Nbe.read_back_nf inner_size (Normal { tp = inner_tp; term = inner_sol }) in

    (* Printf.printf "  Got inner solution %s\n" (Syntax.pp inner); *)
    (* Printf.printf " %s inner_sol = %s\n" (S.show_metavar meta) (Domain.show inner_sol); *)

    (* Now add lambdas *)
    let sol = lams spine inner in
    Printf.printf "Solved %s as %s\n\n%!" (S.show_metavar meta) (S.pp sol);
    let sem_sol = Nbe.eval sol (env_to_sem_env entry.context) in
    (* Printf.printf "  | %s\n" (Domain.show sem_sol); *)
    Meta.solve meta sem_sol sol

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
        unify ~env ~size ~tp ~mode dom1 dom2;
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
    , Neutral { term = { head = Meta (m1, sub1) } as left }
    , Neutral { term = { head = Meta (m2, sub2) } as right } ->
        if m1 = m2
        then unify_ne ~env ~size ~mode ~tp left right
        else S.todo "solve meta in terms of another meta"

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

    (* Tymod *)
    | _, Tymod (mu1, t1), Tymod (mu2, t2) ->
        if not @@ MT.eq_mod mu1 mu2 then
            elab_error (Modality_mismatch
                { left = mu1; right = mu2; desc = Left_right; term = None });
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
        check_mod_eq x.mod1 y.mod1 Left_right None;
        check_mod_eq x.mod2 y.mod2 Left_right None;
        unify_tp ~env ~size ~mode x.argtp y.argtp;
        let (mot_var, mot_env) =
            add_var ~size ~mode ~mu:x.mod1 ~tp:(D.Tymod (x.mod2, x.argtp)) env in
        let mot_x = Nbe.do_clos' x.motive mot_var in
        let mot_y = Nbe.do_clos' y.motive mot_var in
        unify_tp ~env:mot_env ~size:(size + 1) ~mode mot_x mot_y;
        let (body_var, body_env) =
            add_var ~size ~mode ~mu:(MT.compm (x.mod1, x.mod2)) ~tp:x.argtp env in
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
        unify_sp ~env ~size ~mode xs ys
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
        (* List.iter2 (fun x y -> unify_nf ~env ~size ~mode x y) sub1 sub2 *)
        unify_sub ~env ~size ~mode ~meta:m1 sub1 sub2

    (* TODO: this isn't the correct type :( *)
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
        | Term { md } :: ctx'
        , lazy (D.Normal { tp; term = x }) :: left'
        , lazy (D.Normal { term = y }) :: right' ->
            unify ~env ~size ~tp ~mode:md x y;
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


(* ============================================================================
   Elaboration (check and infer)
============================================================================ *)

let rec check_tp ~env:(env : env) ~size:(size : int) ~term:(term : preterm) ~mode:(mode : mode) : Syntax.t =
    check ~env ~size ~tp:(D.Uni ()) ~term ~mode

and check ~env:(env : env) ~size:(size : int) ~tp:(tp : Domain.t) ~term:(term : preterm) ~mode:(mode : mode) : Syntax.t =
    match term, Nbe.force size tp with
    | Nat, Uni _ -> Nat
    (* TODO: universe levels *)
    | Uni l, Uni _ -> Uni l

    | Pi (mu, dom, cod), (Uni _ as tp) ->
        check_mode mode (MT.cod_mod mu mode) Expected_inferred ~modality:mu term;
        let new_env = M mu :: env and new_mode = MT.dom_mod mu mode in
        let dom' = check ~env:new_env ~size ~tp ~term:dom ~mode:new_mode in
        let dom_sem = Nbe.eval dom' (env_to_sem_env env) in
        let (var, new_env) = add_var ~size ~mode ~mu ~tp:dom_sem env in
        let cod' = check ~env:new_env ~size:(size + 1) ~term:cod ~mode ~tp in
        S.Pi (mu, dom', cod')

    | Lam (nu, t), Pi (mu, dom, cod) ->
        let _ = match nu with
            | Some nu -> check_mod_eq nu mu Expected_inferred (Some term)
            | None -> ()
        in
        let (var, new_env) = add_var ~size ~mode ~mu ~tp:dom env in
        let sem_cod = Nbe.do_clos' cod var in
        let t' = check ~env:new_env ~size:(size + 1) ~tp:sem_cod ~term:t ~mode in
        Lam t'

    | Hole name, tp ->
        (* Printf.printf "got check hole\n%!"; *)
        let tp' = Nbe.read_back_tp size tp in
        Meta.fresh_meta ?name env size tp' tp

    | Mod (mu, t), Tymod (nu, tp) ->
        check_mod_eq nu mu Expected_inferred (Some term);
        (* Since Tymod (mu, tp) is valid in this mode, the following check
           should be redundant *)
        check_mode mode (MT.cod_mod mu mode) Expected_inferred term;
        let new_env = M mu :: env and new_mode = MT.dom_mod mu mode in
        let t' = check ~env:new_env ~size:size ~tp ~mode:new_mode ~term:t in
        Mod (mu, t')

    | Pair (fst, snd), Sig (fst_tp, snd_clos) ->
        let sem_env = env_to_sem_env env in
        let fst' = check ~env ~size ~tp:fst_tp ~term:fst ~mode in
        let sem_fst = lazy (Nbe.eval fst' sem_env) in
        let snd_tp = Nbe.do_clos snd_clos sem_fst in
        let snd' = check ~env ~size ~tp:snd_tp ~term:snd ~mode in
        Pair (fst', snd')

    (* TODO: this doesn't work since if the scrutinee is a variable then it
       appears in the context of the metavariable in the motive twice *)
    (* This is effectively the same as the infer case, howevever this allows us
       to unify the motive with the expected type first, which lets us solve
       the motive if the scrutinee is a variables *)
    (* | Letmod x, _ -> *)
    (*     let sem_env = env_to_sem_env env in *)
    (**)
    (*     (* Infer the type of the scrutinee, and check it is a Tymod *) *)
    (*     let (scr_tp, scr) = *)
    (*         infer ~env:(M x.mod1 :: env) ~size *)
    (*             ~term:x.scrutinee ~mode:(MT.dom_mod x.mod1 mode) in *)
    (*     let inner_tp = *)
    (*         match Nbe.force size scr_tp with *)
    (*         | Tymod (mu, it) -> *)
    (*             check_mod_eq x.mod2 mu Expected_inferred (Some term); *)
    (*             it *)
    (*         | tp -> *)
    (*             let it = Meta.fresh_meta env size (D.Uni ()) in *)
    (*             let sem_it = Nbe.eval it sem_env in *)
    (*             let mod_ty = D.Tymod (x.mod2, sem_it) in *)
    (*             unify_catch ~size ~term:x.scrutinee mod_ty tp Expected_inferred *)
    (*                 (unify_tp ~env ~size ~mode); *)
    (*             sem_it *)
    (*     in *)
    (**)
    (*     (* Elaborate the motive *) *)
    (*     let (mod_var, motive_env) = *)
    (*         add_var ~size ~mode ~mu:x.mod1 ~tp:(Tymod (x.mod2, inner_tp)) env in *)
    (*     let motive = *)
    (*         check_tp ~env:motive_env ~size:(size + 1) ~term:x.motive ~mode:mode in *)
    (*     let motive_clos = D.Clos { env = sem_env; term = motive } in *)
    (**)
    (*     let infer_tp = Nbe.do_clos motive_clos (Nbe.eval scr sem_env) in *)
    (*     unify_catch ~size ~term tp infer_tp Expected_inferred *)
    (*         (unify_tp ~env ~size ~mode); *)
    (**)
    (*     (* Elaborate the body *) *)
    (*     let (body_var, body_env) = *)
    (*         add_var ~size ~mode ~mu:(MT.compm (x.mod1, x.mod2)) ~tp:inner_tp env in *)
    (*     let body_tp = Nbe.do_clos motive_clos (Mod (x.mod2, body_var)) in *)
    (*     let body = *)
    (*         check ~env:body_env ~size:(size + 1) ~tp:body_tp ~term:x.body ~mode in *)
    (*     S.Letmod (x.mod1, x.mod2, motive, body, scr) *)


    | _ ->
        let (tp', term') = infer ~env ~size ~term ~mode in
        unify_catch ~size ~term tp tp' Expected_inferred (unify_tp ~env ~size ~mode);
        term'

and infer
    ~env:(env : env) ~size:(size : int) ~term:(term : preterm)
    ~mode:(mode : mode) : Domain.t * Syntax.t =
    match term with
    | Var i ->
        let (mu, tp, mode', locks) = get_var env i in
        (* if not @@ MT.eq_mode mode mode' *)
        (*     then List.iter print_env env; *)
        check_mode mode mode' Expected_inferred ?modality:mu term;
        begin
            (* For local variables, check for 2-cell *)
            match mu with
            | Some mu -> check_cell mu locks term
            | None -> ()
        end;
        (* Printf.printf "While inferring local %d: got type %s\n%!" i (Domain.show tp); *)
        (tp, Var i)

    | Let (def, body) ->
        let (def_tp, def') = infer ~env ~size ~term:def ~mode in
        let sem_def = Nbe.eval def' (env_to_sem_env env) in
        let new_env =
            add_term ~md:mode ~term:sem_def ~mu:MT.idm ~tp:def_tp ~defined:true env in
        let (body_tp, body') = infer ~env:new_env ~size:(size + 1) ~term:body ~mode in
        (body_tp, S.Let (def', body'))

    | Check (tm, tp) ->
        let tp' = check_tp ~env ~size ~term:tp ~mode in
        let sem_tp = Nbe.eval tp' (env_to_sem_env env) in
        let tm' = check ~env ~size ~tp:sem_tp ~term:tm ~mode in
        (sem_tp, Check (tm', tp'))

    | Zero -> (Nat, Zero)
    | Suc tm ->
        let tm' = check ~env ~size ~tp:Nat ~term:tm ~mode in
        (Nat, Suc tm')

    | Fst p ->
        let (tp, p') = infer ~env ~size ~term:p ~mode in
        let fst_tp = match Nbe.force size tp with
            | Sig (fst, _) -> fst
            | tp' ->
                let sem_env = env_to_sem_env env in
                let fst = Meta.fresh_meta_tp env size in
                let sem_fst = Nbe.eval fst sem_env in
                let (_, snd_env) =
                    add_var ~size ~mode ~mu:MT.idm ~tp:sem_fst env in
                let snd = Meta.fresh_meta_tp snd_env (size + 1) in
                let sigm = D.Sig
                    (sem_fst, D.Clos { term = snd; env = env_to_sem_env env }) in
                unify_catch ~size ~term:p sigm tp' Expected_inferred
                    (unify_tp ~env ~size ~mode);
                sem_fst
        in (fst_tp, Fst p')

    | Snd p ->
        let sem_env = env_to_sem_env env in
        let (tp, p') = infer ~env ~size ~term:p ~mode in
        let snd_clos = match Nbe.force size tp with
            | Sig (_, snd_clos) -> snd_clos
            | tp' ->
                let sem_env = env_to_sem_env env in
                let fst = Meta.fresh_meta_tp env size in
                let sem_fst = Nbe.eval fst sem_env in
                let (_, snd_env) =
                    add_var ~size ~mode ~mu:MT.idm ~tp:sem_fst env in
                let snd = Meta.fresh_meta_tp snd_env (size + 1) in
                let snd_clos = D.Clos { term = snd; env = sem_env } in
                let sigm = D.Sig
                    (sem_fst, snd_clos) in
                unify_catch ~size ~term:p sigm tp' Expected_inferred
                    (unify_tp ~env ~size ~mode);
                snd_clos
        in
        let fst = lazy (Nbe.eval (Fst p') sem_env) in
        (Nbe.do_clos snd_clos fst, Snd p')

    | Ap (mu, fn, arg) ->
        let sem_env = env_to_sem_env env in
        let (fn_tp, fn') = infer ~env ~size ~term:fn ~mode in
        (* If the inferred type is already a Pi, skip unifying it with a new Pi *)
        let mu, dom, cod_clos = match Nbe.force size fn_tp with
            | Pi (nu, dom, cod) ->
                let () = match mu with
                    | Some mu -> check_mod_eq mu nu Expected_inferred (Some term);
                    | None -> ()
                in (nu, dom, cod)
            | _ ->
                (* Printf.printf "unifying type\n%!"; *)
                let mu = match mu with
                    | Some mu -> mu
                    | None -> elab_error (Cant_infer_modality term)
                in
                let dom = Nbe.eval (Meta.fresh_meta_tp env size) sem_env in
                let (_, new_env) = add_var ~size ~mode ~mu ~tp:dom env in
                let cod = Meta.fresh_meta_tp new_env size in
                let cod_clos = D.Clos { term = cod; env = sem_env } in
                let pi = D.Pi (mu, dom, cod_clos) in
                unify_catch ~size ~term:fn pi fn_tp Expected_inferred
                    (unify_tp ~env ~size ~mode);
                (mu, dom, cod_clos)
        in
        (* Printf.printf "Got type of fun\n%!"; *)
        let arg' =
            check ~env:(M mu :: env) ~size ~tp:dom
                ~term:arg ~mode:(MT.dom_mod mu mode) in
        (* Printf.printf "checked argument\n%!"; *)
        let _ = Nbe.eval arg' sem_env in
        (* Printf.printf "evaluated argument\n%!"; *)
        (Nbe.do_clos cod_clos (lazy (Nbe.eval arg' sem_env)), Ap (mu, fn', arg'))

    | Lam (mu, body) ->
        let mu = match mu with
            | Some mu -> mu
            | None -> elab_error (Cant_infer_modality term)
        in
        let arg_env = M mu :: env in
        let arg_meta = Meta.fresh_meta_tp arg_env size in
        let argtp = Nbe.eval arg_meta (env_to_sem_env arg_env) in
        let (var, new_env) = add_var ~size ~mode ~mu ~tp:argtp env in

        let (tp, body') = infer ~env:new_env ~size:(size + 1) ~term:body ~mode in
        let tp' = Nbe.read_back_tp (size + 1) tp in
        (Pi (mu, argtp, Clos { term = tp'; env = env_to_sem_env env }), Lam body')

    | Id (tp, x, y) ->
        let tp' = check_tp ~env ~size ~term:tp ~mode in
        let sem_tp = Nbe.eval tp' (env_to_sem_env env) in
        let x' = check ~env ~size ~tp:sem_tp ~term:x ~mode in
        let y' = check ~env ~size ~tp:sem_tp ~term:y ~mode in
        (D.Uni (), S.Id (tp', x', y'))

    | Refl t ->
        let (tp, t') = infer ~env ~size ~term:t ~mode in
        let sem_t = Nbe.eval t' (env_to_sem_env env) in
        (D.Id (tp, sem_t, sem_t), S.Refl t')

    | Hole name ->
        (* Printf.printf "got infer hole\n%!"; *)
        let tp = Meta.fresh_meta_tp env size in
        let sem_tp = Nbe.eval tp (env_to_sem_env env) in
        let tm = Meta.fresh_meta ?name env size tp sem_tp in
        (sem_tp, tm)

    | TyMod (mu, tp) ->
        check_mode mode (MT.cod_mod mu mode) Expected_inferred term;
        let new_env = M mu :: env and new_mode = MT.dom_mod mu mode in
        let tp' = check_tp ~env:new_env ~size ~term:tp ~mode:new_mode in
        (Uni (), TyMod (mu, tp'))

    | Mod (mu, t) ->
        check_mode mode (MT.cod_mod mu mode) Expected_inferred term;
        let new_env = M mu :: env and new_mode = MT.dom_mod mu mode in
        let (tp, t') = infer ~env:new_env ~size ~term:t ~mode:new_mode in
        (Tymod (mu, tp), Mod (mu, t'))

    | Letmod x ->
        let sem_env = env_to_sem_env env in

        (* Infer the type of the scrutinee, and check it is a Tymod *)
        let (scr_tp, scr) =
            infer ~env:(M x.mod1 :: env) ~size
                ~term:x.scrutinee ~mode:(MT.dom_mod x.mod1 mode) in
        let inner_tp =
            match Nbe.force size scr_tp with
            | Tymod (mu, it) ->
                check_mod_eq x.mod2 mu Expected_inferred (Some term);
                it
            | tp ->
                let it = Meta.fresh_meta_tp env size in
                let sem_it = Nbe.eval it sem_env in
                let mod_ty = D.Tymod (x.mod2, sem_it) in
                unify_catch ~size ~term:x.scrutinee mod_ty tp Expected_inferred
                    (unify_tp ~env ~size ~mode);
                sem_it
        in

        (* Elaborate the motive *)
        let (mod_var, motive_env) =
            add_var ~size ~mode ~mu:x.mod1 ~tp:(Tymod (x.mod2, inner_tp)) env in
        let motive =
            check_tp ~env:motive_env ~size:(size + 1) ~term:x.motive ~mode:mode in
        let motive_clos = D.Clos { env = sem_env; term = motive } in

        (* Elaborate the body *)
        let (body_var, body_env) =
            add_var ~size ~mode ~mu:(MT.compm (x.mod1, x.mod2)) ~tp:inner_tp env in
        let body_tp = Nbe.do_clos' motive_clos (Mod (x.mod2, body_var)) in
        let body =
            check ~env:body_env ~size:(size + 1) ~tp:body_tp ~term:x.body ~mode in

        ( Nbe.do_clos motive_clos (lazy (Nbe.eval scr sem_env))
        , S.Letmod (x.mod1, x.mod2, motive, body, scr))

    | J j ->
        let sem_env = env_to_sem_env env in
        let (eq_tp, eq) = infer ~env ~size ~term:j.eq ~mode in

        let (inner_tp, left, right) = match Nbe.force size eq_tp with
            | Id (tp, x, y) -> (tp, x, y)
            | eq_tp' -> S.todo "infer J/unify with metavariables"
        in
        let (mot_var1, mot_env1) =
            add_var ~size ~mode ~mu:MT.idm ~tp:inner_tp env in
        let (mot_var2, mot_env2) =
            add_var ~size:(size + 1) ~mode ~mu:MT.idm ~tp:inner_tp mot_env1 in
        let (mot_var3, mot_env) =
            add_var ~size:(size + 2) ~mode ~mu:MT.idm
                ~tp:(Id (inner_tp, mot_var1, mot_var2)) mot_env2 in
        let motive = check_tp ~env:mot_env ~size:(size + 3) ~term:j.motive ~mode in

        let (refl_var, refl_env) =
            add_var ~size ~mode ~mu:MT.idm ~tp:inner_tp env in
        let refl_tp =
            Nbe.eval motive
                (D.Val (Lazy.from_val @@ D.Refl refl_var)
                    :: D.Val (Lazy.from_val @@ refl_var)
                    :: D.Val (Lazy.from_val refl_var) :: sem_env)
        in
        let refl =
            check ~env:refl_env ~size:(size + 1) ~tp:refl_tp ~term:j.refl ~mode in

        let tp = Nbe.eval motive
            (D.Val (lazy (Nbe.eval eq sem_env)) :: D.Val (Lazy.from_val right)
                :: D.Val (Lazy.from_val left) :: sem_env) in
        (tp, J (motive, refl, eq))

    | Sig (fst, snd) ->
        let fst' = check_tp ~env ~size ~term:fst ~mode in
        let sem_fst = Nbe.eval fst' (env_to_sem_env env) in
        let (fst_var, new_env) = add_var ~size ~mode ~mu:MT.idm ~tp:sem_fst env in
        let snd' = check_tp ~env:new_env ~size:(size + 1) ~term:snd ~mode in
        (D.Uni (), Sig (fst', snd'))

    | NRec x ->
        let sem_env = env_to_sem_env env in
        let (mot_var, mot_env) = add_var ~size ~mode ~mu:MT.idm ~tp:Nat env in
        let mot = check_tp ~env:mot_env ~size:(size + 1) ~term:x.motive ~mode in
        (* Printf.printf "While inferring NRec, got motive %s\n%!" (S.pp mot); *)
        let mot_clos = D.Clos { term = mot; env = sem_env } in

        let zero_tp = Nbe.do_clos' mot_clos Zero in
        let zero = check ~env ~size ~tp:zero_tp ~term:x.zero ~mode in

        let (suc_var1, suc_env) = add_var ~size ~mode ~mu:MT.idm ~tp:Nat env in
        let mot_var = Nbe.do_clos' mot_clos suc_var1 in
        let (suc_var2, suc_env) =
            add_var ~size:(size + 1) ~mode ~mu:MT.idm ~tp:mot_var suc_env in

        (* Printf.printf "about to check suc\n%!"; *)
        let suc = check ~env:suc_env ~size:(size + 2)
            ~tp:(Nbe.do_clos' mot_clos (Suc suc_var1)) ~term:x.suc ~mode in
        (* Printf.printf "  checked suc\n%!"; *)

        (* Printf.printf "about to check scr\n%!"; *)
        let scr = check ~env ~size ~tp:Nat ~term:x.scr ~mode in
        (* Printf.printf "  checked scr\n%!"; *)
        (Nbe.do_clos mot_clos (lazy (Nbe.eval scr sem_env)), NRec (mot, zero, suc, scr))

    | _ ->
        Printf.eprintf "Unhandled infer term: %s\n" (show_preterm term);
        S.todo "infer other terms"
