# RLTL derivatives

A Lean formalisation of symbolic derivatives for extended regular expressions (ERE), LTL and RLTL, together with their correctness proofs.

## Brief file overview

Listed below is a brief description of each file of the formalisation.

- `Ere/Definitions`: the definition of extended regular expressions (ERE), with intersection, negation and fusion.
- `Ere/Metrics`: the star metric used to show termination of the match semantics.
- `Ere/Semantics`: the standard language-based match semantics `xs ⊫ r`.
- `Ere/Derivative`: nullability, the symbolic derivative `δ r`, and multi-step evaluation.
- `Ere/Correctness`: correctness of the symbolic derivative, `a :: xs ⊫ r ↔ xs ⊫ (δ r)[a]`.
- `Ltl/Definitions`, `Ltl/Derivative`, `Ltl/Semantics`, `Ltl/Correctness`: plain LTL with its symbolic and classical derivatives, semantics, and the derivation theorem.
- `Rltl/Definitions`: contains the definition of RLTL formulas.
- `Rltl/Derivatives`: the symbolic derivative `𝜕 φ` and multi-step evaluation.
- `Rltl/OmegaLanguage`: contains the specification of omega languages.
- `Rltl/Semantics`: the match semantics of RLTL, the expansion laws of `U` and `R`, and algebraic rewrite rules.
- `Rltl/Correctness`: contains the main theorem which connects derivatives with the formal semantics.

Effective Boolean algebras and transition terms are imported from
[symbolic-equivalence](https://github.com/ezhuchko/symbolic-equivalence).

The project dependencies are listed in `lakefile.lean`.

## Dependencies

 - [Lean](https://lean-lang.org/) 4.35.0-rc4
 - [mathlib](https://github.com/leanprover-community/mathlib4/) `v4.35.0-rc4`
 - [symbolic-equivalence](https://github.com/ezhuchko/symbolic-equivalence) `main`

## Building

```
lake build
```
