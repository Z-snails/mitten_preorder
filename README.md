## posetal-mitten

An implementation of MTT with modal dependent products (pi), modal types, dependent sums (sigma),
natural numbers, and a cumulative hierarchy. This implementation correctly handles eta for both pi
and sigma.

This implementation only permits pre-order mode theories so that there is at most one 2-cell between
any pair of modalities.

This implementation has also been extended to include a type checker based on Coquand's semantic
type checker. In order to interact with the normalizer, therefore, one can write a file containing a
list of definitions and commands to normalize various terms.

## Prerequisites

Tested under ocaml 4.07.1 and dune 2.8.5. Sexplib, menhir, ppx_compare and cmdliner libraries need
to be installed.

## How to use it

Building mitten with `make build` or `dune build`. Execute mitten with `dune exec mitten
PATH/TO/FILE`. If there is no output, everything type checked. The commands `normalize` and
`normalize def` print the normalized term.

## For example:

```
let plus : (x : {idm | Nat}) -> (y : {idm | Nat}) -> Nat @ s =
    fun m n ->
    rec n at x -> Nat with
    | zero -> m
    | suc _, p -> suc p

normalize plus {idm, 2} {idm, 2} at Nat @ s

let fib : (x : {idm | Nat}) -> Nat @ s =
    fun n ->
    let worker : Nat * Nat =
      rec n at _ -> Nat * Nat with
      | zero -> pair (1, 0)
      | suc _, p -> pair (plus {idm, (fst p)} {idm, (snd p)}, fst p) in
    snd worker

normalize fib {idm, 25} at Nat @ s
```

A list of other examples may be found in `test/`.

The implementation is derived from [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt).

# Zoe's Reading list

- [x] src/lib/check.ml
- [x] src/lib/concrete_mode_theory.ml
- [x] src/lib/concrete_syntax.ml
- [x] src/lib/domain.ml
- [x] src/lib/driver.ml
- [x] src/lib/grammar.mly
- [x] src/lib/guarded_mode_theory.ml
- [x] src/lib/guarded_mode_theory1.ml
- [x] src/lib/lex.mll
- [x] src/lib/load.ml
- [x] src/lib/mode_theory.ml
- [x] src/lib/nbe.ml
- [x] src/lib/syntax.ml

## Cool things

- Inferring modalities in applications: f {l, x} can now usually be replaced by f x
- Inferring lambdas if the modality is provided
- List unsolved metavariables

## Zoe's TODO list

- [x] Add `force` to `src/lib/check.ml` to allow type-checking metavariables; or
- [ ] Add a pass to replace metavariables with their solutions (this is pretty
  tricky on account of top level definitions using de Bruijn variables)
- [ ] Track when a metavariable m is solved in terms of another metavariable n,
  and when n is solved, update the solution of m
- [ ] Replace remaining uses of `add_term` with `add_var`
- [ ] Copy examples from elab zoo
- [ ] Add pruning (this might allow solving the motive of non-dependent eliminators)
