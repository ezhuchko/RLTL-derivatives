# Lean4 formalization of "Symbolic Automata: 𝜔-Regularity Modulo Theories"

This repo contains the Lean formalization files for the paper "Symbolic Automata: 𝜔-Regularity Modulo Theories".

## Quick start

You can run this formalization online on GitHub codespaces, without installing anything:

  1. Press the comma key (<kbd>,</kbd>) to create a codespace, or just click this link: https://codespaces.new/ezhuchko/RLTL-derivatives
  2. Wait a minute or two for the codespace to be created.
  3. Open the `Regex/Regex.lean` file, which collects all modules of the formalization. Note that if Lean does not produce an error message, it means that the entire formalization compiles and there are no remaining `sorry`'s. 

Alternatively, you can also install Lean on your machine and run the project locally:

  1. Install VS Code and then install the `lean4` extension.
  2. Open the `RLTL-derivatives` folder as the root directory in VS Code.
  3. Open the `Regex/Regex.lean` file, which collects all modules of the formalization.

To build code and proofs from the command line:

```shell
lake update
lake build Regex
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

## Requirements 

- `lake` 5.0.0-6fce8f7 (`lean` 4.7.0)v4.8.0-rc1
- `mathlib` v4.7.0 (`nightly-testing-2024-04-25`)
