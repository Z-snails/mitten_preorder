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
- [x] Add a pass to replace metavariables with their solutions (this is pretty
  tricky on account of top level definitions using de Bruijn variables)
- [ ] Track when a metavariable m is solved in terms of another metavariable n,
  and when n is solved, update the solution of m
- [ ] Replace remaining uses of `add_term` with `add_var`
- [x] Copy examples from elab zoo
- [ ] Add pruning (this might allow solving the motive of non-dependent eliminators)
- [ ] Find reference of proof that solving metavariables works (for pattern fragment)
    - [ ] Read it
- [x] Fix the bug in stream.tt

## Papers on correctness of unification/solving metavariable in pattern fragment

- [ ] https://link.springer.com/chapter/10.1007/3-540-51081-8_104
  - I don't think this will be that useful, it focuses on general unification rather than just solving metavariables

- [ ] https://ncatlab.org/nlab/files/Norell-PracticalDTT.pdf
  - Seems promising, there's a section on correctness and the algorithm seems similar to ours
  - Proves that if unification succeeds then type checking produces well-typed terms
  - Well-typedness for metavariable solution ends up being pretty straightforward

- [ ] https://arxiv.org/abs/1609.09709 Type checking through unification
  - Has a pretty different algorithm

- [ ] https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/22631/NeilLeslieMThesis1993_original_C.pdf?sequence=1
  - Useful defintions
  - Does not unify terms in a dependent type theory

- [ ] Bidirectional Elaboration of Dependently Typed Programs https://dl.acm.org/doi/abs/10.1145/2643135.2643153
  - Maybe has some useful references but I don't think it contains a unification algorithm

- [ ] G. Dowek, T. Hardin, C. Kirchner, and F. Pfenning. Unification via explicit substitutions: The case of higher-order patterns.
  - Seems useful, uses explicit substitutions like MTT
  - Defines normal forms of substitutions --- unclear what these should be for MTT
  - Proves that the solution is well typed in more detail
  - Also proves there is a unique solution iff the problem is in the pattern fragment

- [ ] D. Miller. Unification of simply typed lambda-terms as logic programming. In 8th International Logic Programming Conference, pages 255–269. MIT Press, 1991

- [ ] Unification with extended patterns, Dominic Duggan

- [ ] Pattern Unification for the Lambda Calculus with Linear and Affine Types, Anders Schack-Nielsen, Carsten Schürmann
  - Has similar problems to us in that variables can be available in the problem but not in the solution

### Things to prove

- Solving gives a valid term
    - Term should type check
    - and should solve the problem
- Gives a most general unifier (how is this defined exactly?)
- If there is a solution that makes the program type check, then the solution found should make the program type check

### Thoughts

- For non-modal DTT, I think showing solving metavariables in pattern fragment gives a well-typed solution will be pretty easy
- The difficult part of the proof for MTT will be showing variable accesses are valid, which isn't an issue for non-modal DTT
- Do the locks in the problem/meta context matter?

# Log

## 2025-09-02 16:52

`read_back_meta` was wrong --- it incorrectly changed the size at which each term in the delayed sub was read back at. The fix was to just use the same size for each (since each term in the sub is in the same context)
