module S = Syntax
module D = Domain
module MT = Mode_theory

open Meta.Check_env

type mode = MT.mode
type modality = MT.m

open Unify

(* Errors *)
let while_elaborating (n : Concrete_syntax.ident) (f : unit -> 'a) : 'a =
    try
        f ()
    with
    | Elab_error e -> raise (Elab_error (While_elaborating (n, e)))

(* Elaboration *)

let check_mode (left : mode) (right : mode) (desc : error_desc) ?modality term =
    if not (MT.eq_mode left right)
    then elab_error (Mode_mismatch { left; right; desc; modality; term })

let check_cell (lesser : modality) (greater : modality) (term : preterm) =
    if not (MT.leq lesser greater)
    then elab_error (Missing_2cell { lesser; greater; term })

let rec check_tp
    ~env:(env : env) ~size:(size : int) ~term:(term : preterm)
    ~mode:(mode : mode) : Syntax.t =
    check ~env ~size ~tp:(D.Uni ()) ~term ~mode

and check
    ~env:(env : env) ~size:(size : int) ~tp:(tp : Domain.t)
    ~term:(term : preterm) ~mode:(mode : mode) : Syntax.t =
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
       appears in the context of the metavariable in the motive twice. Pruning
       would solve this in for non-dependent motives *)
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
