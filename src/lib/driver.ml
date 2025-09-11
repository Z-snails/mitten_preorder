module CS = Concrete_syntax
module D = Domain
module E = Elab
module U = Unify
module M = Mode_theory
module S = Syntax
module Check_env = Meta.Check_env

type env = Env of {size : int; check_env : Check_env.env; bindings : string list}

let initial_env = Env {size = 0; check_env = []; bindings = []}

type check_output =
  | CheckedDef of CS.ident * S.t * S.t * env
  | NF_term of S.t * S.t
  | NF_def of CS.ident * S.t
  | Quit

let update_env env = function
  | CheckedDef (_, _, _, env') -> env'
  | NF_term _ | NF_def _ | Quit -> env

(** Print a value, and return true if we should continue checking the program *)
let output (Env { bindings; _ }) =
  let open Sexplib in
  let show ?indent s =
    Syntax.to_sexp (List.map (fun x -> Sexp.Atom x) bindings) s
    |> Sexp.to_string_hum ?indent
  in
  function
  | CheckedDef (name, tp, tm, _) ->
    Printf.printf "%s\n  : %s\n  = %s\n\n" name (show tp ~indent:5) (show tm ~indent:5);
  | NF_term (s, t) ->
    Printf.printf "Computed normal form of\n  %s\nas\n  %s\n%!"
      (show s ~indent:3) (show t ~indent:3);
  | NF_def (name, t) ->
    Printf.printf "Computed normal form of [%s]:\n  %s\n%!" name (show t ~indent:3);
  | Quit -> ()

let find_idx key =
  let rec go i = function
    | [] -> raise (Check.Type_error (Check.Misc ("Unbound variable: " ^ key)))
    | x :: xs -> if x = key then i else go (i + 1) xs in
  go 0

let rec int_to_term = function
  | 0 -> U.Zero
  | n -> U.Suc (int_to_term (n - 1))

let rec unravel_spine f = function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec bind (env : string list) : Concrete_syntax.t -> U.preterm = function
  | CS.Var i -> U.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    U.Let (bind env tp, bind (name :: env) body)
  | CS.Check {term; tp} -> U.Check (bind env term, bind env tp)
  | CS.Nat -> U.Nat
  | CS.Suc t -> U.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = Binder {name = mot_name; body = mot_body};
        zero;
        suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat } ->
    U.NRec {
      motive = bind (mot_name :: env) mot_body;
      zero = bind env zero;
      suc = bind (suc_name2 :: suc_name1 :: env) suc_body;
      scr = bind env nat
    }
  | CS.Pi (mu, src, Binder {name; body}) ->
    U.Pi (M.bind_m mu, bind env src, bind (name :: env) body)
  | CS.Lam (BinderN {names = []; body}) ->
    bind env body
  | CS.Lam (BinderN {names = (mu, x) :: names; body}) ->
    let lam = CS.Lam (BinderN {names; body}) in
    U.Lam (Option.map M.bind_m mu, bind (x :: env) lam)
  | CS.Ap (f, args) ->
    List.map
      (fun (mu, t) f -> U.Ap (Option.map M.bind_m mu, f, bind env t)) args
    |> unravel_spine (bind env f)
  | CS.Sig (tp, Binder {name; body}) ->
    U.Sig (bind env tp, bind (name :: env) body)
  | CS.Pair (l, r) -> U.Pair (bind env l, bind env r)
  | CS.Fst p -> U.Fst (bind env p)
  | CS.Snd p -> U.Snd (bind env p)
  | CS.J
      { mot = Binder3 {name1 = left; name2 = right; name3 = prf; body = mot_body};
       refl = Binder {name = refl_name; body = refl_body};
       eq } ->
    U.J {
      motive = bind (prf :: right :: left :: env) mot_body;
      refl = bind (refl_name :: env) refl_body;
      eq = bind env eq;
    }
  | CS.Id (tp, left, right) ->
    U.Id (bind env tp, bind env left, bind env right)
  | CS.Refl t -> U.Refl (bind env t)
  | CS.Uni i -> U.Uni ()
  | CS.TyMod (mu, tp) -> U.TyMod (M.bind_m mu, bind env tp)
  | CS.Mod (mu, tp) -> U.Mod (M.bind_m mu, bind env tp)
  | CS.Letmod (mu, nu, Binder {name; body = tp}, Binder {name = mod_var; body}, def) ->
    U.Letmod {
      mod1 = M.bind_m mu; mod2 = M.bind_m nu;
      motive = bind (name :: env) tp;
      scrutinee = bind env def;
      body = bind (mod_var :: env) body;
    }
  | CS.Hole n -> U.Hole n

type elab_output =
  | ElabDef of { name: CS.ident; def: Syntax.t; tp: Syntax.t; md: M.mode }
  | NormalizeDef of CS.ident
  | NormalizeTerm of { term: Syntax.t; tp: Syntax.t; md: M.mode }
  | ElabAxiom of { name: CS.ident; tp: Syntax.t; md: M.mode }
  | Quit

let elab_decl (Env { size; check_env; bindings } as env) = function
  | CS.Def { name; def; tp; md } ->
    let bind_md = M.bind_mode md in
    let def = bind bindings def in
    let tp = bind bindings tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    let tp2 = Elab.while_elaborating ~size name
      (fun _ -> Elab.check_tp ~size ~env:check_env ~term:tp ~mode:bind_md) in
    let sem_tp = Nbe.eval tp2 sem_env in

    let def2 = Elab.while_elaborating ~size name
      (fun _ -> Elab.check ~size ~env:check_env ~tp:sem_tp ~term:def ~mode:bind_md) in

    let sem_def = Nbe.eval def2 sem_env in

    let new_entry =
      Check_env.TopLevel
        { name; level = size; term = sem_def; tp = sem_tp; md = bind_md } in

    ( ElabDef { name; def = def2; tp = tp2; md = bind_md }
    , Env {
        size = size + 1;
        check_env = new_entry :: check_env;
        bindings = name :: bindings })

  | CS.NormalizeDef name ->
    ignore @@ find_idx name bindings;
    (NormalizeDef name, env)

  | CS.NormalizeTerm {term; tp; md} ->
    let bind_md = M.bind_mode md in
    let term = bind bindings term in
    let tp = bind bindings tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    let tp2 = Elab.check_tp ~size ~env:check_env ~term:tp ~mode:bind_md in
    let sem_tp = Nbe.eval tp2 sem_env in

    let term2 = Elab.check ~size ~env:check_env ~tp:sem_tp ~term:term ~mode:bind_md in

    (NormalizeTerm { term = term2; tp = tp2; md = bind_md }, env)

  | CS.Axiom {name; tp; md} ->
    let bind_md = M.bind_mode md in
    let tp = bind bindings tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    let tp2 = Elab.check_tp ~size ~env:check_env ~term:tp ~mode:bind_md in
    let sem_tp = Nbe.eval tp2 sem_env in

    let new_entry =
      Check_env.TopLevel
        { name; level = size; term = D.Neutral {tp = sem_tp; term = D.axiom name sem_tp}
        ; tp = sem_tp; md = bind_md
        }
    in
    ( ElabAxiom { name; tp = tp2; md = bind_md }
    , Env
        { size = size + 1; check_env = new_entry :: check_env
        ; bindings = name :: bindings })

  | CS.Quit -> (Quit, env)

let process_decl (Env { size; check_env; bindings }) = function
  | ElabDef { name; def; tp; md } ->
    let tp = Meta.remove_solved check_env tp in
    let def = Meta.remove_solved check_env def in
    let sem_env = Check_env.env_to_sem_env check_env in

    Check.check_tp ~size ~env:check_env ~term:tp ~m:md;
    let sem_tp = Nbe.eval tp sem_env in

    Check.check ~size ~env:check_env ~term:def ~tp:sem_tp ~m:md;
    let sem_def = Nbe.eval def sem_env in

    (* Printf.printf "  checked def3\n%!"; *)

    let new_entry =
      Check_env.TopLevel
        { name; level = size; term = sem_def; tp = sem_tp; md } in
    CheckedDef (name, tp, def,
      Env {
        size = size + 1;
        check_env = new_entry :: check_env;
        bindings = name :: bindings })

  | NormalizeDef name ->
    begin
      match List.nth check_env (find_idx name bindings) with
      | Check_env.TopLevel { term; tp; md = _ } ->
        NF_def (name, Nbe.read_back_nf 0 (D.Normal {term; tp}))
      | _ -> failwith "Unreachable"
    end

  | NormalizeTerm {term; tp; md} ->
    let tp = Meta.remove_solved check_env tp in
    let term = Meta.remove_solved check_env term in
    let sem_env = Check_env.env_to_sem_env check_env in

    Check.check_tp ~size ~env:check_env ~term:tp ~m:md;
    let sem_tp = Nbe.eval tp sem_env in

    Check.check ~size ~env:check_env ~term:term ~tp:sem_tp ~m:md;
    let sem_term = Nbe.eval term sem_env in

    let norm_term = Nbe.read_back_nf 0 (D.Normal {term = sem_term; tp = sem_tp}) in
    NF_term (term, norm_term)

  | ElabAxiom { name; tp; md } ->
    let tp = Meta.remove_solved check_env tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    Check.check_tp ~size ~env:check_env ~term:tp ~m:md;
    let sem_tp = Nbe.eval tp sem_env in

    let new_entry =
      Check_env.TopLevel
        { name; level = size; term = D.Neutral {tp = sem_tp; term = D.axiom name sem_tp}
        ; tp = sem_tp; md
        }
    in
    CheckedDef (name, tp, S.Axiom (name, tp),
      Env
        { size = size + 1; check_env = new_entry :: check_env
        ; bindings = name :: bindings })

  | Quit -> Quit

let rec elab_sign env = function
  | [] -> []
  | CS.Quit :: _ -> [Quit]
  | d :: ds ->
    let (d', env) = elab_decl env d in
    let ds' = elab_sign env ds in
    d' :: ds'

let rec check_sign ?(env = initial_env) = function
  | [] | Quit :: _ -> env
  | d :: ds ->
    let o = process_decl env d in
    output env o;
    check_sign ~env:(update_env env o) ds

let process_sign ?(env = initial_env) ds =
  elab_sign env ds |> check_sign ~env

(* TODO: variable names *)
let print_unsolved_holes (_ : env) =
  let pp_domain ~counter ~names (size : int) (t : Domain.t) =
    Syntax.pp ~counter ~names (Nbe.read_back_tp size t) in

  let rec pp_env ~counter (env : Check_env.env) =
    match env with
    | Check_env.Term x :: env' ->
      let (ctx, names, size) = pp_env ~counter env' in
      incr counter; let v = "x" ^ string_of_int !counter in
      ( Printf.sprintf "%s :%s %s"
        v (M.mod_pp x.mu) (pp_domain ~counter ~names size x.tp)
        :: ctx
      , v :: names
      , size + 1
      )
    | Check_env.TopLevel x :: env' ->
      let (ctx, names, size) = pp_env ~counter env' in
      (ctx, x.name :: names, size + 1)
    | Check_env.M mu :: env' ->
      let (ctx, names, size) = pp_env ~counter env' in
      (Printf.sprintf "lock %s" (Mode_theory.mod_pp mu) :: ctx, names, size)
    | [] -> ([], [], 0)
  in

  let print_meta (m, e : S.metavar * Meta.entry) : unit =
    let counter = ref 0 in
    let (ctx, names, size) = pp_env ~counter e.context in
    List.iter print_endline (List.rev ctx);
    assert (size = e.size);
    print_endline "====================";
    Printf.printf "%s : %s\n\n"
      (Syntax.show_metavar m) (Syntax.pp ~counter ~names e.tp);
  in

  let unsolved_holes =
    List.filter
      (function (n, (e : Meta.entry)) -> Option.is_none e.value)
      (Meta.all_metas ())
  in

  match unsolved_holes with
  | [] -> Printf.printf "No unsolved metavariables"
  | _ ->
    begin
      Printf.printf "Unsolved metavariables:\n\n";
      List.iter print_meta unsolved_holes
    end
