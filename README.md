# Lean4 formalization of "Symbolic Automata: 𝜔-Regularity Modulo Theories"

This repo contains the Lean formalization files for the paper "Symbolic Automata: 𝜔-Regularity Modulo Theories".

## Quick start

a) You can run this formalization **online on GitHub codespaces**, without installing anything:

  1. Press the comma key (<kbd>,</kbd>) to create a codespace, or just click this link: https://codespaces.new/ezhuchko/RLTL-derivatives
  2. Wait a minute or two for the codespace to be created.
  3. Open the `Regex.lean` file, which collects all modules of the formalization. Note that if Lean does not produce an error message, it means that the entire formalization compiles and there are no remaining `sorry`'s. 

b) Alternatively, you can also install Lean **locally on your machine** and run the project locally:

  1. Install VS Code and then install the `lean4` extension.
  2. Open the `RLTL-derivatives` folder as the root directory in VS Code.
  3. Open the `Regex.lean` file, which collects all modules of the formalization.

c) To build code and proofs from the **command line**:

  1. Install the Lean version manager [`elan`](https://github.com/leanprover/elan):
```shell
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source $HOME/.elan/env
```

  2. Download prebuilt binaries for mathlib:
```shell
lake exe cache get
```

  2. Build the project:
```shell
lake build
```

## Brief file overview

Listed below is a brief description of each file of the formalization.

- `Definitions`: main definitions common to all files: Effective Boolean Algebra, ERE, RLTL.
- `EREMatchSemantics`: the standard language-based match semantics.
- `Metrics`: metrics on regular expression to show termination of theorems/definitions.
- `OmegaLanguage`: contains the specification of omega languages.
- `RLTL`: contains the main `derivation` theorem.
- `TTerm`: main definitions and lemmas about transition terms.

The project dependencies are listed in `lakefile.lean`.

## Key definitions 

* `ERE`: The class of extended regular expressions (ERE) which includes intersection and negation.
* `RLTL`: The combination of linear temporal logic and extended regular expressions modulo an Effective Boolean Algebra.
* `OneStep`: a predicate which looks one derivative step ahead in a given regular expression.
* `ERE.models`: the matching relation for regular expressions based on language-based semantics. The notation `xs ⊫ R` expresses that a string `xs` matches the language of `R`. 
* `InOmegaLanguage`: the matching relation for omega-regular languages. The notation `w ∈* R` expresses that a stream `w` matches the language of `R`.
* `RLTL.models`: the matching relation for `RLTL` formulas. The notation `w |= f` expresses that a stream `w` matches the RLTL formula `f`.

## List of claims 

- `RLTL.lean` contains the main `derivation` theorem which corresponds to Theorem 4 from Section 7.6 of the paper. The theorem relies on properties of the key definitions listed above such as correctness (`denoteOneStep`) and completeness (`denoteOneStep'`) of `OneStep`, the equivalence between classical language-based semantics and derivatives (`equivalenceDer`) and the correctness and completeness properties of omega-regular language semantics (`regexOmegaClosure`). 

## Dependencies

 - [Lean](https://lean-lang.org/) 4.7.0
 - [mathlib](https://github.com/leanprover-community/mathlib4/) revision [a5485f37](https://github.com/leanprover-community/mathlib4/tree/a5485f370ebd36f0c873820b1717d3d03b43b35e) from April 21 2024

The Lean version manager elan and the build tool lake will automatically download these dependency versions when you run `lake build`.

Lean has minimal platform requirements.  The instructions provided above will work on Ubuntu 24.04 (x86-64) with git and curl installed.  Other platforms, including Windows and macOS, are supported by Lean as well.  Please see the [Lean documentation](https://lean-lang.org/lean4/doc/setup.html) for more details on platform support.