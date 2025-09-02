module Syn = Syntax

module D = Domain
open Mode_theory

exception Nbe_failed of string

(* clos_mod is completly unused *)
let rec clos_mod (D.Clos {term; env}) mu = D.Clos {term = term; env = D.M mu :: env}

and gen_do_clos (D.Clos {term; env}) a = eval term (a :: env)
and do_clos clos a = gen_do_clos clos (D.Val a)

and gen_do_clos2 (D.Clos2 {term; env}) a1 a2 = eval term ( a2 :: a1 :: env)
and do_clos2 clos a1 a2 = gen_do_clos2 clos (Val a1) (Val a2)

and gen_do_clos3 (D.Clos3 {term; env}) a1 a2 a3 = eval term (a3 :: a2 :: a1 :: env)
and do_clos3 clos a1 a2 a3 = gen_do_clos3 clos (Val a1) (Val a2) (Val a3)

(* TODO: all eliminators should use force: see test/03-holes.tt for tests *)
(* Or: be very careful to call force before calling do_<elim> *)
and do_nrec tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc m -> do_clos2 suc m (do_nrec tp zero suc m)
  | D.Neutral {term = e; _} ->
    let final_tp = do_clos tp n in
    D.Neutral {tp = final_tp; term = D.elim (D.NRec { motive = tp; zero; suc }) e}
  | _ -> raise (Nbe_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp; term = ne} ->
    begin
      match tp with
      | D.Sig (t, _) -> D.Neutral {tp = t; term = D.elim D.Fst ne}
      | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")
    end
  | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")

and do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp; term = ne} ->
    begin
      match tp with
      | D.Sig (_, clo) ->
        let fst = do_fst p in
        D.Neutral {tp = do_clos clo fst; term = D.elim D.Snd ne}
      | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")
    end
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")


and do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Pi (mu, src, dst) ->
        let dst = do_clos dst a in
        D.Neutral
          { tp = dst; term = D.elim (D.Ap (mu, D.Normal { tp = src; term = a })) e }
      | _ ->
        (* Printf.printf "in do_ap, got unexpected %s" (D.show tp); *)
        raise (Nbe_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Nbe_failed "Not a Pi in do_ap")

and do_j mot refl eq =
  match eq with
  | D.Refl t -> do_clos refl t
  | D.Neutral {tp; term} ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Neutral
          { tp = do_clos3 mot left right eq;
            term = D.elim (D.J { motive = mot; refl; tp; left; right }) term }
      | _ -> raise (Nbe_failed "Not an Id in do_j")
    end
  | _ -> raise (Nbe_failed "Not a Refl or Neutral value in do_j")

and do_letmod nu tyclos body def =
  match def with
  | D.Mod (_, tm1) -> do_clos body tm1
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Tymod (mu, argtp) ->
        let tp2 = do_clos tyclos (D.Neutral {tp = D.Tymod (mu, argtp); term = e}) in
        D.Neutral
          { tp = tp2; term =
            D.elim (D.Letmod { mod1 = mu; mod2 = nu; motive = tyclos; body; argtp }) e }
      | _ -> raise (Nbe_failed "Not a TyMod in do_mod")
    end
  | _ -> raise (Nbe_failed "Not a Mod or Neutral in do_mod")

and eval t (env : D.env) =
  match t with
  | Syn.Var id -> D.env_val env id
  (* | Syn.Var id -> *)
  (*   begin *)
  (*   try D.env_val env id *)
  (*   with *)
  (*   | e -> *)
  (*       Printf.printf "Variable %d in env of length %d\n" id (List.length env); *)
  (*       raise e *)
  (*     end *)
  | Syn.Let (def, body) -> eval body ((D.Val (eval def env)) :: env)
  | Syn.Check (term, _) -> eval term env
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env)
  | Syn.NRec (tp, zero, suc, n) ->
    do_nrec
      (Clos {term = tp; env})
      (eval zero env)
      (Clos2 {term = suc; env})
      (eval n env)
  | Syn.Pi (mu, src, dest) ->
    D.Pi (mu, (eval src (D.M mu :: env)), (Clos {term = dest; env}))
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (mu, t1, t2) -> do_ap (eval t1 env) (eval t2 (D.M mu :: env))
  | Syn.Uni i -> D.Uni i
  | Syn.Sig (t1, t2) -> D.Sig (eval t1 env, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)
  | Syn.Refl t -> D.Refl (eval t env)
  | Syn.Id (tp, left, right) -> D.Id (eval tp env, eval left env, eval right env)
  | Syn.J (mot, refl, eq) ->
    do_j (D.Clos3 {term = mot; env}) (D.Clos {term = refl; env}) (eval eq env)
  | Syn.TyMod (mu, t) ->
    let new_env = D.M mu :: env in
    D.Tymod (mu, eval t new_env)
  | Syn.Mod (mu, t) ->
    let new_env = D.M mu :: env in
    D.Mod (mu, eval t new_env)
  | Syn.Letmod (_ ,nu ,tyfam , body , def) ->
    do_letmod nu
      (D.Clos {term = tyfam; env = env})
      (D.Clos {term = body; env = env}) (eval def env)
  | Syn.Axiom (str, tp) ->
    D.Neutral {tp = eval tp env; term = D.axiom str (eval tp env)}
  | Syn.Meta (m, sub) ->
    let e = Meta.lookup m in
    let size = List.length @@ List.filter (function
      | D.M _ -> false
      | D.Val _ -> true) env in
    let sp1 = eval_sub sub ~env ~size ~meta:e in
    (* Printf.printf "While evaluating Syn.Meta. Got sub\n%s\n%!" *)
      (* (String.concat "\n" (List.map (Domain.show _ Lazy.force) (D.untp_sub sp1))); *)
    let sub = (D.untp_sub sp1, size - e.size) in
    match e.value with
    | Some (v, _) -> subst sub v
    | None -> D.Neutral
      { tp = subst sub e.tp
      ; term = D.meta m sp1 }

(* sp is a cons list, ctx is a snoc list, so we need to reverse ctx first *)
(* TODO: think about size: when subst-ing the types, each entry in context is
   at a different size *)
and eval_sub
  ~env:(env : D.env) ~size:(size : int) ~(meta : Meta.entry)
  (sp : Syntax.t list) : D.tp_sub =

  (* let var_off = size - meta.size in *)

  let rec go sp (ctx : Meta.Check_env.env) (sub : D.t Lazy.t list) (msize : int) =
    match sp, ctx with
    | [], [] ->
      assert (msize = meta.size);
      []

    | (t :: sp'), (Term { tp } :: ctx') ->
      let sem_t = lazy (eval t env) in
      (* TODO: what should the var offset be? *)
      lazy (D.Normal { tp = subst (sub, size - msize) tp; term = Lazy.force sem_t })
        :: go sp' ctx' (List.append sub [sem_t]) (msize + 1)

    (* The type of global variables shouldn't depend on values in the
       substitution, so we can skip subst for global variables. Also global
       variables are already associated with a term, so we can skip evaluating
       them *)
    | _ :: sp', TopLevel { tp; term } :: ctx' ->
      lazy (D.Normal { tp; term })
        :: go sp' ctx' (List.append sub [lazy term]) (msize + 1)

    | _, M _ :: ctx' -> go sp ctx' sub msize
    | _ -> failwith
      "The length of the spine and number of variables in the context don't match"
  in

  (* Printf.printf "sp has len %d, ctx has len %d\n%!" (List.length sp) (List.length meta.context); *)

  (* Printf.printf "eval_sub: sp = %s\n%!" (String.concat ", " (List.map Syntax.pp sp)); *)
  (* Printf.printf " env has length %d\n%!" (List.length env); *)
  (* List.iter (function | D.Val t -> Printf.printf " %s\n%!" (D.show t) | _ -> ()) env; *)

  let x = go sp (List.rev meta.context) [] 0 in

  (* Printf.printf " result = \n%!"; *)
  (* List.iter (function lazy (D.Normal { term }) -> Printf.printf " %s\n%!" (Domain.show term)) x; *)

  x

and do_elim (elim : Domain.elim) (tm : Domain.t) : Domain.t =
    match elim, tm with
    | Ap (mu, Normal a), tm -> do_ap tm a.term
    | Fst, tm -> do_fst tm
    | Snd, tm -> do_snd tm
    | NRec x, tm -> do_nrec x.motive x.zero x.suc tm
    | Letmod x, tm -> do_letmod x.mod1 x.motive x.body tm
    | J x, tm -> do_j x.motive x.refl tm

and do_spine (spine : Domain.elim list) (tm : Domain.t) : Domain.t =
    List.fold_right do_elim spine tm

and subst_clos (sub : D.sub * int) (D.Clos { term; env }) : D.clos =
    D.Clos { term; env = subst_env sub env }
and subst_clos2 (sub : D.sub * int) (D.Clos2 { term; env }) : D.clos2 =
    D.Clos2 { term; env = subst_env sub env }
and subst_clos3 (sub : D.sub * int) (D.Clos3 { term; env }) : D.clos3 =
    D.Clos3 { term; env = subst_env sub env }

and subst_env (sub : D.sub * int) (env : Domain.env) : Domain.env =
    List.map (function
        | D.Val v -> D.Val (subst sub v)
        | D.M mu -> D.M mu
    ) env

and subst_nf (sub : D.sub * int) (Normal { tp; term } : D.nf) : D.nf =
    Normal { tp = subst sub tp; term = subst sub term }

and subst (sub : D.sub * int) (t : Domain.t) : Domain.t = match t with
    | D.Lam clos -> D.Lam (subst_clos sub clos)
    | D.Neutral { tp; term } -> subst_ne sub tp term
    | D.Nat -> D.Nat
    | D.Zero -> D.Zero
    | D.Suc t -> D.Suc (subst sub t)
    | D.Pi (m, dom, cod) -> D.Pi (m, subst sub dom, subst_clos sub cod)
    | D.Sig (fst, snd) -> D.Sig (subst sub fst, subst_clos sub snd)
    | D.Pair (fst, snd) -> D.Pair (subst sub fst, subst sub snd)
    | D.Refl t -> D.Refl (subst sub t)
    | D.Id (tp, x, y) -> D.Id (subst sub tp, subst sub x, subst sub y)
    | D.Uni l -> D.Uni l
    | D.Tymod (m, tp) -> D.Tymod (m, subst sub tp)
    | D.Mod (m, tm) -> D.Mod (m, subst sub tm)

(* Since a substitution may introduce a redex, we may have to do some evaluation *)
and subst_ne (sub : D.sub * int) (tp : Domain.t) (ne : Domain.ne) : Domain.t =
    let spine = List.map (subst_elim sub) ne.spine in
    match ne.head with
    | Var i -> begin
        match List.nth_opt (fst sub) i with
        | Some (lazy t) -> do_spine spine t
        | None ->
            D.Neutral
                { tp = subst sub tp
                ; term = { head = D.Var (i + snd sub); spine } }
        end
    | Axiom (n, t) ->
        D.Neutral { tp = subst sub tp; term = { head = D.Axiom (n, t); spine } }
    | Meta (m, sp) ->
        D.Neutral
            { tp = subst sub tp
            ; term =
              { head = D.Meta (m, List.map (Lazy.map (subst_nf sub)) sp)
              ; spine } }

and subst_elim (sub : D.sub * int) (elim : D.elim) : D.elim =
    match (elim : D.elim) with
    | D.Ap (mu, x) -> D.Ap (mu, subst_nf sub x)
    | D.Fst -> D.Fst
    | D.Snd -> D.Snd
    | D.NRec _ -> Syn.todo "subst_elim/NRec"
    | D.Letmod _ -> Syn.todo "subst_elim/Letmod"
    | D.J _ -> Syn.todo "subst_elim/J"

(** Update any metavariables in the head of a term *)
let rec force (size : int) (t : Domain.t) : Domain.t =
  match t with
  Neutral { tp; term = { head = Meta (m, sub); spine } as term } ->
    begin
      let entry = Meta.lookup m in
      let off = size - entry.size in
      match entry.value with
      | None -> Neutral { tp = force size tp; term }
      | Some v ->
        let v' = subst (D.untp_sub sub, off) (fst v) in
        force size (do_spine spine v')
    end
  | _ -> t

let force_nf (size : int) (Normal t : Domain.nf) : Domain.nf =
  Normal { tp = force size t.tp; term = force size t.term }

(* Nested matching necessary. We cannot match just on nf, since we need to push tp before *)
let rec read_back_nf size (D.Normal { tp; term = v }) =
  (* Functions *)
  match force size tp with
  | Pi (_, src, dest) ->
    let arg = D.mk_var src size in
    let nf = D.Normal {tp = do_clos dest arg; term = do_ap v arg} in
    Syn.Lam (read_back_nf (size + 1) nf)
  (* Pairs *)
  | D.Sig (fst, snd) ->
    let fst' = do_fst v in
    let snd = do_clos snd fst' in
    let snd' = do_snd v in
    Syn.Pair
      (read_back_nf size (D.Normal { tp = fst; term = fst'}),
       read_back_nf size (D.Normal { tp = snd; term = snd'}))
  (* Numbers *)
  | D.Nat ->
    begin
      match force size v with
      | D.Zero -> Syn.Zero
      | D.Suc nf ->
        Syn.Suc (read_back_nf size (D.Normal {tp = D.Nat; term = nf}))
      | D.Neutral {term = ne; _} -> read_back_ne size ne
      | _ -> raise (Nbe_failed "Natural number expected in read_back_nf")
    end
  (* Types *)
  | D.Uni i ->
    begin
      match force size v with
      | D.Nat -> Syn.Nat
      | D.Pi (mu, src, dest) ->
        let var = D.mk_var src size in
        Syn.Pi (mu,
                read_back_nf size (D.Normal {tp = D.Uni i; term = src}),
                read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos dest var}))
      | D.Sig (fst, snd) ->
        let var = D.mk_var fst size in
        Syn.Sig
          (read_back_nf size (D.Normal {tp = D.Uni i; term = fst}),
           read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos snd var}))
      | D.Uni j -> Syn.Uni j
      | D.Id (tp, le, ri) ->
        Syn.Id (
          read_back_nf size (D.Normal {tp = D.Uni i; term = tp}),
          read_back_nf size (D.Normal {tp = tp; term = le}),
          read_back_nf size (D.Normal {tp = tp; term = ri})
        )
      | D.Tymod (mu, tp) -> Syn.TyMod (mu, read_back_nf size (D.Normal {tp = D.Uni i; term = tp }))
      | D.Neutral {term = ne; _} -> read_back_ne size ne
      | _ -> raise (Nbe_failed ("element of universe expected in read_back_nf\n False term: "))
    end
  | D.Neutral _ as tp ->
    begin
      match force size v with
      | D.Neutral {term = ne; _} -> read_back_ne size ne
      | v ->
        Printf.printf "Whoopsies, unexpected term: %s\n  at type: %s\n" (Domain.show v) (Domain.show tp);
        raise (Nbe_failed "Neutral expected for Neutral Type in read_back_nf")
    end
  (* Id *)
  | D.Id (tp, _, _) ->
    begin
      match force size v with
      | D.Refl term ->
        Syn.Refl (read_back_nf size (D.Normal {tp; term}))
      | D.Neutral {term; _} ->
        read_back_ne size term
      | _ -> raise (Nbe_failed "No Refl or Neutral in read_back_nf")
    end
  (* Modal types *)
  | D.Tymod (_, tp1) ->
    begin
      match force size v with
      | D.Mod (mu, w) -> Syn.Mod (mu, read_back_nf size (D.Normal {tp = tp1; term = w }))
      | D.Neutral {term = ne; _} -> read_back_ne size ne
      | _ -> raise (Nbe_failed "element of modal type expected in read_back_nf")
    end
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")


and read_back_tp size d =
  match force size d with
  | D.Neutral {term; _} -> read_back_ne size term
  | D.Nat -> Syn.Nat
  | D.Pi (mu, src, dest) ->
    let var = D.mk_var src size in
    Syn.Pi (mu, read_back_tp size src, read_back_tp (size + 1) (do_clos dest var))
  | D.Sig (fst, snd) ->
    let var = D.mk_var fst size in
    Syn.Sig (read_back_tp size fst, read_back_tp (size + 1) (do_clos snd var))
  | D.Id (tp, left, right) ->
    Syn.Id
      (read_back_tp size tp,
       read_back_nf size (D.Normal {tp; term = left}),
       read_back_nf size (D.Normal {tp; term = right}))
  | D.Uni k -> Syn.Uni k
  | D.Tymod (mu, tp) -> Syn.TyMod (mu, read_back_tp size tp)
  | _ -> raise (Nbe_failed "Not a type in read_back_tp")

and read_back_head (size : int) (head : D.head) = match head with
  | D.Var x -> Syn.Var (size - (x + 1))
  | D.Meta (m, sub) -> read_back_meta size m sub
  | D.Axiom (n, tp) -> Syn.Axiom (n, read_back_tp size tp)

and read_back_meta (size : int) (meta : Syn.metavar) (sub : D.tp_sub) =
  let rec go (size : int) (ctx : Meta.Check_env.env_entry list) (sub : D.tp_sub) =
    match ctx, sub with
    | [], [] -> []
    (* Local variables are read back normally *)
    | Term _ :: ctx', lazy t :: sub' ->
      read_back_nf size t :: go (size + 1) ctx' sub'
    (* Global variables can be read back directly *)
    | TopLevel { level } :: ctx', _ :: sub' ->
      let ix = size - (level - 1) in
      Syn.Var ix :: go (size + 1) ctx' sub'
    | M _ :: ctx', _ -> go size ctx' sub
    | _ -> failwith "Unreachable in read_back_meta"
  in
  let entry = Meta.lookup meta in
  Syn.Meta (meta, go size (List.rev entry.context) sub)

and read_back_elim (size : int) (elim : D.elim) (tm : Syn.t) = match elim with
  | D.Ap (mu, x) -> Syn.Ap (mu, tm, read_back_nf size x)
  | D.Fst -> Syn.Fst tm
  | D.Snd -> Syn.Snd tm

  | D.NRec { motive; zero; suc } ->
    let tp_var = D.mk_var D.Nat size in
    let applied_tp = do_clos motive tp_var in
    let tp' = read_back_tp (size + 1) applied_tp in

    (* Motive at zero and suc *)
    let zero_tp = do_clos motive D.Zero in
    let applied_suc_tp = do_clos motive (D.Suc tp_var) in

    let suc_var = D.mk_var applied_tp (size + 1) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' = read_back_nf (size + 2) (D.Normal { tp = applied_suc_tp; term = applied_suc }) in

    Syn.NRec
      (tp'
      , read_back_nf size (D.Normal { tp = zero_tp; term = zero })
      , suc', tm
      )

  | D.Letmod { mod1; mod2; motive; body; argtp } ->
    (* ..., _ :mod1 Tymod (mod2, argtp) |- motive : U *)
    let motive' = do_clos motive (D.mk_var (D.Tymod (mod2, argtp)) size) in
    (* ..., _ :mod12 argtp |- body : motive[p . mod mod2 q] *)
    let body_tp = do_clos motive (D.Mod (mod2, D.mk_var argtp size)) in
    let body' = D.Normal { tp = body_tp; term = do_clos body (D.mk_var argtp size) } in
    Syn.Letmod
      ( mod1, mod2
      , read_back_tp (size + 1) motive'
      , read_back_nf (size + 1) body'
      , tm
      )

  | D.J { motive; refl; tp } ->
    let mot_var1 = D.mk_var tp size and mot_var2 = D.mk_var tp (size + 1) in
    let mot_var3 = D.mk_var (D.Id (tp, mot_var1, mot_var2)) (size + 2) in
    let mot_syn = read_back_tp (size + 3) (do_clos3 motive mot_var1 mot_var2 mot_var3) in
    let refl_var = D.mk_var tp size in
    let refl_syn = read_back_nf (size + 1) (D.Normal
        { tp = do_clos3 motive refl_var refl_var (D.Refl refl_var)
        ; term = do_clos refl refl_var
        }) in
    Syn.J
      ( mot_syn
      , refl_syn
      , tm
      )

and read_back_spine (size : int) (spine : D.elim list) (tm : Syn.t) =
  match spine with
  | [] -> tm
  | e :: es -> read_back_elim size e (read_back_spine size es tm)

and read_back_ne size ne =
  read_back_spine size (ne.spine) (read_back_head size ne.head)
  (* match ne with *)
  (* | D.Var x -> Syn.Var (size - (x + 1)) *)
  (* | D.Ap (mu, ne, arg) -> Syn.Ap (mu, read_back_ne size ne, read_back_nf size arg) *)
  (* | D.NRec (tp, zero, suc, n) -> *)
  (*   let tp_var = D.mk_var D.Nat size in *)
  (*   let applied_tp = do_clos tp tp_var in *)
  (*   let zero_tp = do_clos tp D.Zero in *)
  (*   let applied_suc_tp = do_clos tp (D.Suc tp_var) in *)
  (*   let tp' = read_back_tp (size + 1) applied_tp in *)
  (*   let suc_var = D.mk_var applied_tp (size + 1) in *)
  (*   let applied_suc = do_clos2 suc tp_var suc_var in *)
  (*   let suc' = *)
  (*     read_back_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in *)
  (*   Syn.NRec *)
  (*     (tp', *)
  (*      read_back_nf size (D.Normal {tp = zero_tp; term = zero}), *)
  (*      suc', *)
  (*      read_back_ne size n) *)
  (* | D.Fst ne -> Syn.Fst (read_back_ne size ne) *)
  (* | D.Snd ne -> Syn.Snd (read_back_ne size ne) *)

  (* | D.Letmod (mu, nu, tyfam, clos, argtp, ne) -> *)
  (*   let tp = do_clos tyfam (D.Tymod (mu, D.mk_var argtp size)) in *)
  (*   let tm = D.Normal {tp = tp; term = do_clos clos (D.mk_var argtp size)} in *)
  (*   Syn.Letmod (mu, nu, read_back_tp (size + 1) tp, read_back_nf (size + 1) tm, read_back_ne size ne) *)

  (* | D.J (mot, refl, tp, _, _, eq) -> *)
  (*   let mot_var1 = D.mk_var tp size in *)
  (*   let mot_var2 = D.mk_var tp (size + 1) in *)
  (*   let mot_var3 = D.mk_var (D.Id (tp, mot_var1, mot_var2)) (size + 2) in *)
  (*   let mot_syn = read_back_tp (size + 3) (do_clos3 mot mot_var1 mot_var2 mot_var3) in *)
  (*   let refl_var = D.mk_var tp size in *)
  (*   let refl_syn = *)
  (*     read_back_nf *)
  (*       (size + 1) *)
  (*       (D.Normal {term = do_clos refl refl_var; tp = do_clos3 mot refl_var refl_var (D.Refl refl_var)}) in *)
  (*   let eq_syn = read_back_ne size eq in *)
  (*   Syn.J (mot_syn, refl_syn, eq_syn) *)
  (* | D.Axiom (str, tp) -> Syn.Axiom (str, read_back_tp size tp) *)


(* Check two normal forms are (definitionally) equal *)
let rec check_nf m size nf1 nf2 =
  match force_nf size nf1, force_nf size nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (mu, src1, dest1); term = f1},
    D.Normal {tp = D.Pi (nu, _, dest2); term = f2} ->
    let arg = D.mk_var src1 size in
    let nf1 = D.Normal {tp = do_clos dest1 arg; term = do_ap f1 arg} in
    let nf2 = D.Normal {tp = do_clos dest2 arg; term = do_ap f2 arg} in
    eq_mod mu nu && check_nf m (size + 1) nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sig (fst1, snd1); term = p1},
    D.Normal {tp = D.Sig (fst2, snd2); term = p2} ->
    let p11, p21 = do_fst p1, do_fst p2 in
    let snd1 = do_clos snd1 p11 in
    let snd2 = do_clos snd2 p21 in
    let p12, p22 = do_snd p1, do_snd p2 in
    check_nf m size (D.Normal {tp = fst1; term = p11}) (D.Normal {tp = fst2; term = p21})
    && check_nf m size (D.Normal {tp = snd1; term = p12}) (D.Normal {tp = snd2; term = p22})
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero},
    D.Normal {tp = D.Nat; term = D.Zero} -> true
  | D.Normal {tp = D.Nat; term = D.Suc nf1},
    D.Normal {tp = D.Nat; term = D.Suc nf2} ->
    check_nf m size (D.Normal {tp = D.Nat; term = nf1}) (D.Normal {tp = D.Nat; term = nf2})
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Nat; term = D.Neutral {term = ne2; _}}-> check_ne m size ne1 ne2
  (* Modalities *)
  | D.Normal {tp = D.Tymod (_, tp); term = D.Mod (mu, tm)},
    D.Normal {tp = D.Tymod (_, tp1); term = D.Mod (nu, tm1)} ->
    eq_mod mu nu &&
    let new_m = dom_mod mu m in
    check_nf new_m size (D.Normal {tp = tp; term = tm}) (D.Normal {tp = tp1; term = tm1})
  | D.Normal {tp = D.Tymod (mu, tp); term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Tymod (nu, tp1); term = D.Neutral {term = ne2; _}} ->
    eq_mod mu nu &&
    let new_m = dom_mod mu m in
    check_tp new_m ~subtype:false size tp tp1 && check_ne new_m size ne1 ne2
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (_, _, _); term = D.Refl term2} ->
    check_nf m size (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  | D.Normal {tp = D.Id _; term = D.Neutral {term = term1; _}},
    D.Normal {tp = D.Id _; term = D.Neutral {term = term2; _}} ->
    check_ne m size term1 term2
  (* Types *)
  | D.Normal {tp = D.Uni _; term = D.Nat},
    D.Normal {tp = D.Uni _; term = D.Nat} -> true
  | D.Normal {tp = D.Uni i; term = D.Pi (mu, src1, dest1)},
    D.Normal {tp = D.Uni j; term = D.Pi (nu, src2, dest2)} ->
    let var = D.mk_var src1 size in
    eq_mod mu nu &&
    let new_m = dom_mod mu m in
    check_nf new_m size (D.Normal {tp = D.Uni i; term = src1}) (D.Normal {tp = D.Uni j; term = src2})
    && check_nf m (size + 1) (D.Normal {tp = D.Uni i; term = do_clos dest1 var})
      (D.Normal {tp = D.Uni j; term = do_clos dest2 var})
  | D.Normal {tp = D.Uni i; term = D.Sig (src1, dest1)},
    D.Normal {tp = D.Uni j; term = D.Sig (src2, dest2)} ->
    let var = D.mk_var src1 size in
    check_nf m size (D.Normal {tp = D.Uni i; term = src1}) (D.Normal {tp = D.Uni j; term = src2})
    && check_nf m (size + 1) (D.Normal {tp = D.Uni i; term = do_clos dest1 var})
      (D.Normal {tp = D.Uni j; term = do_clos dest2 var})
  | D.Normal {tp = D.Uni i; term = D.Tymod (mu, tp)},
    D.Normal {tp = D.Uni j; term = D.Tymod (nu, tp1)} ->
    eq_mod mu nu &&
    let new_m = dom_mod mu m in
    check_nf new_m size (D.Normal {tp = D.Uni i; term = tp}) (D.Normal {tp = D.Uni j; term = tp1})
  | D.Normal {tp = D.Uni _; term = D.Uni j},
    D.Normal {tp = D.Uni _; term = D.Uni j'} -> j = j'

  | D.Normal { tp = D.Uni _; term = D.Id (tp1, x1, y1) },
    D.Normal { tp = D.Uni _; term = D.Id (tp2, x2, y2) } ->
    check_tp m ~subtype:false size tp1 tp2 &&
    check_nf m size (D.Normal { tp = tp1; term = x1 }) (D.Normal { tp = tp2; term = x2 }) &&
    check_nf m size (D.Normal { tp = tp1; term = y1 }) (D.Normal { tp = tp2; term = y2 })

  | D.Normal {tp = D.Uni _; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Uni _; term = D.Neutral {term = ne2; _}} -> check_ne m size ne1 ne2
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne2; _}} -> check_ne m size ne1 ne2
  | _ -> false

and check_head (m : mode) (size : int) (h1 : D.head) (h2 : D.head) =
  match h1, h2 with
  | D.Var x, D.Var y -> x = y
  | D.Meta (m1, sub1), D.Meta (m2, sub2) ->
    m1 = m2 && check_sub m size m1 sub1 sub2
  | D.Axiom (n1, _), D.Axiom (n2, _) -> String.equal n1 n2
  | _, _ -> false

and check_sub
  (m : mode) (size : int) (meta : Syn.metavar) (left : D.tp_sub) (right : D.tp_sub) =

  let rec go
    (size : int) (ctx : Meta.Check_env.env_entry list)
    (left : D.tp_sub) (right : D.tp_sub) =
    match ctx, left, right with
    | [], [], [] -> true
    | Term { mu } :: ctx', lazy x :: xs, lazy y :: ys ->
      check_nf (dom_mod mu m) size x y
        && go (size + 1) ctx' xs ys
    (* We don't need to check global variables are the same, since the 2 subs
       are in the same context *)
    | TopLevel _ :: ctx', _ :: xs, _ :: ys -> go (size + 1) ctx' xs ys
    | _ -> failwith "Unreachable"
  in
  let entry = Meta.lookup meta in
  go size (List.rev entry.context) left right


and check_elim (m : mode) (size : int) (e1 : D.elim) (e2 : D.elim) =
  match e1, e2 with
  | Ap (mu1, x), Ap (mu2, y) ->
    (* The modalities should be the same, but check anyway *)
    assert (eq_mod mu1 mu2);
    (* TODO: This used to be check_nf m size x1 x2, but I think it should be this *)
    check_nf (dom_mod mu1 m) size x y

  | Fst, Fst -> true
  | Snd, Snd -> true

  | NRec x, NRec y -> Syn.todo "NRec"

  | Letmod x, Letmod y ->
    let arg_m = dom_mod (compm (x.mod1, x.mod2)) m in
    eq_mod x.mod1 y.mod1 && eq_mod x.mod2 y.mod2 &&
    check_tp arg_m ~subtype:false size x.argtp y.argtp &&
    let mot_var = D.mk_var (Tymod (x.mod2, x.argtp)) size in
    check_tp m ~subtype:false (size + 1)
      (do_clos x.motive mot_var) (do_clos y.motive mot_var) &&
    let body_var = D.mk_var x.argtp size in
    let body_tp = do_clos x.motive (D.Mod (x.mod2, body_var)) in
    check m size ~tp:body_tp (do_clos x.body body_var) (do_clos y.body body_var)

  | J x, J y ->
    check_tp ~subtype:false m size x.tp y.tp &&

    let mot_var1 = D.mk_var x.tp size in
    let mot_var2 = D.mk_var x.tp (size + 1) in
    let mot_var3 = D.mk_var (D.Id (x.tp, mot_var1, mot_var2)) (size + 2) in
    check_tp ~subtype:false m (size + 3)
      (do_clos3 x.motive mot_var1 mot_var2 mot_var3)
      (do_clos3 y.motive mot_var1 mot_var2 mot_var3) &&

    let refl_var = D.mk_var x.tp size in
    let refl_tp = do_clos3 x.motive refl_var refl_var (D.Refl refl_var) in
    check m size ~tp:refl_tp
      (do_clos x.refl refl_var) (do_clos y.refl refl_var)

  | _, _ -> false

and check_ne (m : mode) (size : int) (x : D.ne) (y : D.ne) =
  match x.spine, y.spine with
  | [], [] -> check_head m size x.head y.head
  | x1 :: xs, y1 :: ys ->
    check_elim m size x1 y1 &&
    (* Letmod changes the mode of the rest of the spine and head *)
    let new_m = match x1 with
      | Letmod x -> dom_mod x.mod1 m
      | _ -> m
    in check_ne new_m size { x with spine = xs } { y with spine = ys }
  | _ -> false

and check (m : mode) (size : int) ~tp:(tp : Domain.t) (x : Domain.t) (y : Domain.t) =
  check_nf m size (Normal { tp; term = x }) (Normal { tp; term = y })

(* Check two neutral values are (definitionally) equal *)
(* and check_ne m size ne1 ne2 = *)
(*   match ne1, ne2 with *)
(*   | D.Var x, D.Var y -> x = y *)
(*   | D.Ap (_, ne1, arg1), D.Ap (_, ne2, arg2) -> *)
(*     check_ne m size ne1 ne2 && check_nf m size arg1 arg2 *)

(*   | D.NRec (tp1, zero1, suc1, n1), D.NRec (tp2, zero2, suc2, n2) -> *)
(*     let tp_var = D.mk_var D.Nat size in *)
(*     let applied_tp1, applied_tp2 = do_clos tp1 tp_var, do_clos tp2 tp_var in *)
(*     let zero_tp = do_clos tp1 D.Zero in *)
(*     let applied_suc_tp = do_clos tp1 (D.Suc tp_var) in *)
(*     let suc_var1 = D.mk_var applied_tp1 (size + 1) in *)
(*     let suc_var2 = D.mk_var applied_tp2 (size + 1) in *)
(*     let applied_suc1 = do_clos2 suc1 tp_var suc_var1 in *)
(*     let applied_suc2 = do_clos2 suc2 tp_var suc_var2 in *)
(*     check_tp m ~subtype:false (size + 1) applied_tp1 applied_tp2 *)
(*     && check_nf m size (D.Normal {tp = zero_tp; term = zero1}) (D.Normal {tp = zero_tp; term = zero2}) *)
(*     && check_nf m (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc1}) *)
(*       (D.Normal {tp = applied_suc_tp; term = applied_suc2}) *)
(*     && check_ne m size n1 n2 *)

(*   | D.Fst ne1, D.Fst ne2  -> check_ne m size ne1 ne2 *)
(*   | D.Snd ne1, D.Snd ne2 -> check_ne m size ne1 ne2 *)
(*   | D.Letmod (mu, nu, tyclos, clos, argty, ne), *)
(*     D.Letmod (mu1, nu1, tyclos1, clos1, _, ne1) -> *)
(*     let arg = D.mk_var argty size in *)
(*     let applied_ty = do_clos tyclos (D.Mod (mu, arg)) in *)
(*     let applied_ty1 = do_clos tyclos1 (D.Mod (mu, arg)) in *)
(*     let applied_tm = do_clos clos arg in *)
(*     let applied_tm1 = do_clos clos1 arg in *)
(*     eq_mod mu mu1 && eq_mod nu nu1 && *)
(*     check_nf m (size + 1) (D.Normal {tp = applied_ty; term = applied_tm}) (D.Normal {tp = applied_ty1; term = applied_tm1}) *)
(*     && let new_m = dom_mod mu m in *)
(*     check_ne new_m size ne ne1 *)
(*   | D.J (mot1, refl1, tp1, left1, right1, eq1), *)
(*     D.J (mot2, refl2, tp2, left2, right2, eq2) -> *)
(*     check_tp m ~subtype:false size tp1 tp2 && *)
(*     check_nf m size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp2; term = left2}) && *)
(*     check_nf m size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp2; term = right2}) && *)
(*     let mot_var1 = D.mk_var tp1 size in *)
(*     let mot_var2 = D.mk_var tp1 (size + 1) in *)
(*     let mot_var3 = D.mk_var (D.Id (tp1, left1, right1)) (size + 2) in *)
(*     check_tp m ~subtype:false (size + 3) (do_clos3 mot1 mot_var1 mot_var2 mot_var3) (do_clos3 mot2 mot_var1 mot_var2 mot_var3) && *)
(*     let refl_var = D.mk_var tp1 size in *)
(*     check_nf *)
(*       m *)
(*       (size + 1) *)
(*       (D.Normal {term = do_clos refl1 refl_var; tp = do_clos3 mot1 refl_var refl_var (D.Refl refl_var)}) *)
(*       (D.Normal {term = do_clos refl2 refl_var; tp = do_clos3 mot2 refl_var refl_var (D.Refl refl_var)}) && *)
(*     check_ne m size eq1 eq2 *)
(*   | D.Axiom (str1, _), D.Axiom (str2, _) -> String.equal str1 str2 *)
(*   | _ -> false *)

(* Check two types are equal *)
and check_tp m ~subtype size d1 d2 =
  match force size d1, force size d2 with
  | D.Neutral {term = term1; _}, D.Neutral {term = term2; _} ->
    check_ne m size term1 term2
  | D.Nat, D.Nat -> true
  | D.Pi (mu, src, dest), D.Pi (nu, src', dest') ->
    let var = D.mk_var src' size in
    let new_m = dom_mod mu m in
    eq_mod mu nu && check_tp new_m ~subtype size src' src &&
    check_tp m ~subtype (size + 1) (do_clos dest var) (do_clos dest' var)
  | D.Sig (fst, snd), D.Sig (fst', snd') ->
    let var = D.mk_var fst size in
    check_tp m ~subtype size fst fst' &&
    check_tp m ~subtype (size + 1) (do_clos snd var) (do_clos snd' var)
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp m ~subtype size tp1 tp2 &&
    check_nf m size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf m size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Uni k, D.Uni j -> if subtype then k <= j else k = j
  | D.Tymod (mu, tp), D.Tymod (nu, tp1) ->
    let new_m = dom_mod mu m in
    eq_mod mu nu && check_tp new_m ~subtype size tp tp1
  | _ -> false

(* To normalize an arbitrary term G |- M : A we need to reflect the context G in an initial environment. We include this for completeness, though the function "normalize" is in fact not used. For equality checking we use the more efficient "check_nf" resp. "check_np" functions.
 * Furthermore, toplevel definitions are handled a bit differently (see proc_decl in the driver.ml)
 * Otherwise, the type checker doesn't let the user specify open terms. *)
let rec initial_env env =
  match env with
  | [] -> []
  | Syn.Ty t :: env ->
    let env' = initial_env env in
    let d = D.mk_var (eval t env') (Syn.env_length env) in
    (D.Val d) :: env'
  | Syn.Mo mu :: env ->
    D.M mu :: initial_env env

let normalize ~env ~term ~tp =
  let env' = initial_env env in
  let tp' = eval tp env' in
  let term' = eval term env' in
  read_back_nf (List.length env') (D.Normal {tp = tp'; term = term'})
