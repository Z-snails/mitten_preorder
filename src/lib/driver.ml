module CS = Concrete_syntax
module D = Domain
module E = Elab
module M = Mode_theory
module S = Syntax
module Check_env = Meta.Check_env

type env = Env of {size : int; check_env : Check_env.env; bindings : string list}

let initial_env = Env {size = 0; check_env = []; bindings = []}

type output =
  | Def of CS.ident * S.t * S.t * env
  | NF_term of S.t * S.t
  | NF_def of CS.ident * S.t
  | Quit

let update_env env = function
  | Def (_, _, _, env') -> env'
  | NF_term _ | NF_def _ | Quit -> env

let output (Env { bindings; _ }) =
  let open Sexplib in
  let show ?indent s =
    Syntax.to_sexp (List.map (fun x -> Sexp.Atom x) bindings) s
    |> Sexp.to_string_hum ?indent
  in
  function
  | Def (name, tp, tm, _) ->
    Printf.printf "%s\n  : %s\n  = %s\n\n" name (show tp ~indent:5) (show tm ~indent:5)
  | NF_term (s, t) ->
    Printf.printf "Computed normal form of\n  %s\nas\n  %s\n%!"
      (show s ~indent:3) (show t ~indent:3)
  | NF_def (name, t) ->
    Printf.printf "Computed normal form of [%s]:\n  %s\n%!" name (show t ~indent:3)
  | Quit -> exit 0

let find_idx key =
  let rec go i = function
    | [] -> raise (Check.Type_error (Check.Misc ("Unbound variable: " ^ key)))
    | x :: xs -> if String.equal x key then i else go (i + 1) xs in
  go 0

let rec int_to_term = function
  | 0 -> E.Zero
  | n -> E.Suc (int_to_term (n - 1))

let rec unravel_spine f = function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec bind (env : string list) : Concrete_syntax.t -> Elab.preterm = function
  | CS.Var i -> E.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    E.Let (bind env tp, bind (name :: env) body)
  | CS.Check {term; tp} -> E.Check (bind env term, bind env tp)
  | CS.Nat -> E.Nat
  | CS.Suc t -> E.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = Binder {name = mot_name; body = mot_body};
        zero;
        suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat } ->
    E.NRec {
      motive = bind (mot_name :: env) mot_body;
      zero = bind env zero;
      suc = bind (suc_name2 :: suc_name1 :: env) suc_body;
      scr = bind env nat
    }
  | CS.Pi (mu, src, Binder {name; body}) ->
    E.Pi (M.bind_m mu, bind env src, bind (name :: env) body)
  | CS.Lam (BinderN {names = []; body}) ->
    bind env body
  | CS.Lam (BinderN {names = (mu, x) :: names; body}) ->
    let lam = CS.Lam (BinderN {names; body}) in
    E.Lam (Option.map M.bind_m mu, bind (x :: env) lam)
  | CS.Ap (f, args) ->
    List.map
      (fun (mu, t) f -> E.Ap (Option.map M.bind_m mu, f, bind env t)) args
    |> unravel_spine (bind env f)
  | CS.Sig (tp, Binder {name; body}) ->
    E.Sig (bind env tp, bind (name :: env) body)
  | CS.Pair (l, r) -> E.Pair (bind env l, bind env r)
  | CS.Fst p -> E.Fst (bind env p)
  | CS.Snd p -> E.Snd (bind env p)
  | CS.J
      { mot = Binder3 {name1 = left; name2 = right; name3 = prf; body = mot_body};
       refl = Binder {name = refl_name; body = refl_body};
       eq } ->
    E.J {
      motive = bind (prf :: right :: left :: env) mot_body;
      refl = bind (refl_name :: env) refl_body;
      eq = bind env eq;
    }
  | CS.Id (tp, left, right) ->
    E.Id (bind env tp, bind env left, bind env right)
  | CS.Refl t -> E.Refl (bind env t)
  | CS.Uni i -> E.Uni ()
  | CS.TyMod (mu, tp) -> E.TyMod (M.bind_m mu, bind env tp)
  | CS.Mod (mu, tp) -> E.Mod (M.bind_m mu, bind env tp)
  | CS.Letmod (mu, nu, Binder {name; body = tp}, Binder {name = mod_var; body}, def) ->
    E.Letmod {
      mod1 = M.bind_m mu; mod2 = M.bind_m nu;
      motive = bind (name :: env) tp;
      scrutinee = bind env def;
      body = bind (mod_var :: env) body;
    }
  | CS.Hole n -> E.Hole n

let process_decl (Env { size; check_env; bindings })  = function
  | CS.Def { name; def; tp; md } ->
    (* Printf.printf "About to check %s\n%!" name; *)
    let bind_md = M.bind_mode md in
    let def = bind bindings def in
    let tp = bind bindings tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    (* Elaborate the type, then check the resulting value is well-typed *)
    let tp2 = Elab.while_elaborating name
      (fun _ -> Elab.check_tp ~size ~env:check_env ~term:tp ~mode:bind_md) in
    let tp3 = Meta.remove_solved check_env tp2 in
    (* Printf.printf "  got tp3\n%!"; *)
    Check.check_tp ~size ~env:check_env ~term:tp3 ~m:bind_md;
    let sem_tp = Nbe.eval tp3 sem_env in

    (* Printf.printf "  checked tp3\n%!"; *)

    (* Repeat with the definition *)
    let def2 = Elab.while_elaborating name
      (fun _ -> Elab.check ~size ~env:check_env ~tp:sem_tp ~term:def ~mode:bind_md) in
    (* Printf.printf "  got def2\n%!"; *)
    let def3 = Meta.remove_solved check_env def2 in
    (* Printf.printf "  got def3\n%!"; *)
    Check.check ~size ~env:check_env ~term:def3 ~tp:sem_tp ~m:bind_md;
    let sem_def = Nbe.eval def3 sem_env in

    (* Printf.printf "  checked def3\n%!"; *)

    let new_entry =
      Check_env.TopLevel
        { name; level = size; term = sem_def; tp = sem_tp; md = bind_md } in
    Def (name, tp3, def3,
      Env {
        size = size + 1;
        check_env = new_entry :: check_env;
        bindings = name :: bindings })

  | CS.NormalizeDef name ->
    let err = Check.Type_error (Check.Misc ("Unbound variable: " ^ name)) in
    begin
      match List.nth_opt check_env (find_idx name bindings) with
      | Some (Check_env.TopLevel { term; tp; md = _ }) ->
        NF_def (name, Nbe.read_back_nf 0 (D.Normal {term; tp}))
      | _ -> raise err
    end

  | CS.NormalizeTerm {term; tp; md} ->
    let bind_md = M.bind_mode md in
    let term = bind bindings term in
    let tp = bind bindings tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    let tp2 = Elab.check_tp ~size ~env:check_env ~term:tp ~mode:bind_md in
    Check.check_tp ~size ~env:check_env ~term:tp2 ~m:bind_md;
    let sem_tp = Nbe.eval tp2 sem_env in

    let term2 = Elab.check ~size ~env:check_env ~tp:sem_tp ~term:term ~mode:bind_md in
    Check.check ~size ~env:check_env ~term:term2 ~tp:sem_tp ~m:bind_md;
    let sem_term = Nbe.eval term2 sem_env in
    let norm_term = Nbe.read_back_nf 0 (D.Normal {term = sem_term; tp = sem_tp}) in
    NF_term (term2, norm_term)

  | CS.Axiom {name; tp; md} ->
    let bind_md = M.bind_mode md in
    let tp = bind bindings tp in
    let sem_env = Check_env.env_to_sem_env check_env in

    let tp2 = Elab.check_tp ~size ~env:check_env ~term:tp ~mode:bind_md in
    let tp3 = Meta.remove_solved check_env tp2 in
    Check.check_tp ~size ~env:check_env ~term:tp3 ~m:bind_md;
    let sem_tp = Nbe.eval tp2 sem_env in

    let new_entry =
      Check_env.TopLevel
        { name; level = size; term = D.Neutral {tp = sem_tp; term = D.axiom name sem_tp}
        ; tp = sem_tp; md = bind_md
        }
    in
    Def (name, tp3, S.Axiom (name, tp3),
      Env
        { size = size + 1; check_env = new_entry :: check_env
        ; bindings = name :: bindings })

  | CS.Quit -> Quit

let rec process_sign ?(env = initial_env) = function
  | [] -> env
  | d :: ds ->
    (* Printf.printf "About to process_decl\n%!"; *)
    let o = process_decl env d in
    (* Printf.printf "About to output\n%!"; *)
    output env o;
    process_sign ~env:(update_env env o) ds

(* TODO: variable names *)
let print_unsolved_holes (_ : env) =
  let pp_domain ~counter ~names (size : int) (t : Domain.t) =
    Syntax.pp ~counter ~names (Nbe.read_back_tp size t) in

  let rec pp_env ~counter (env : Check_env.env) =
    match env with
    | Check_env.Term x :: env' ->
      let (ctx, names, size) = pp_env ~counter env' in
      incr counter; let v = "x" ^ string_of_int !counter in
      ( Printf.sprintf "%s : %s" v (pp_domain ~counter ~names size x.tp) :: ctx
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
    Printf.printf "%s : %s\n\n" (Syntax.show_metavar m)
      (pp_domain ~counter ~names e.size e.tp);
    Printf.printf "Got names: %s\n" (String.concat ", " names);
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
