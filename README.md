## Brief file overview

Listed below is a brief description of each file of the formalization.

- `EffectiveBooleanAlgebra`: main definition of effective boolean algebras. 
- `TTerm`: main definitions and lemmas about transition terms.
- `Definitions`: contains the definitions of Extended Regular Expressions (ERE) and RLTL.
- `Metrics`: some simple metrics to show termination of theorems/definitions.
- `ERE`: the standard language-based match semantics and symbolic derivation rules for ERE.
- `OmegaLanguage`: contains the specification of omega languages.
- `RLTL`: contains the main theorem which connects derivative based unfolding with the formal semantics.

The project dependencies are listed in `lakefile.lean`.

## Dependencies

 - [Lean](https://lean-lang.org/) 4.7.0
 - [mathlib](https://github.com/leanprover-community/mathlib4/) revision [a5485f37](https://github.com/leanprover-community/mathlib4/tree/a5485f370ebd36f0c873820b1717d3d03b43b35e) from April 21 2024

The Lean version manager elan and the build tool lake will automatically download these dependency versions when you run `lake build`.

Lean has minimal platform requirements.  The instructions provided above will work on Ubuntu 24.04 (x86-64) with git and curl installed.  Other platforms, including Windows and macOS, are supported by Lean as well.  Please see the [Lean documentation](https://lean-lang.org/lean4/doc/setup.html) for more details on platform support.
