# Lean4 formalization of RLTL

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

## List of claims

- `RLTL.lean` contains the main `derivation` theorem which corresponds to Theorem 4 from Section 7.6 of the paper. The theorem relies on properties of the key definitions listed above such as correctness (`denoteOneStep`) and completeness (`denoteOneStep'`) of `OneStep`, the equivalence between classical language-based semantics and derivatives (`equivalenceDer`) and the correctness and completeness properties of omega-regular language semantics (`regexOmegaClosure`).

## Evaluation instructions

  1. Open the formalization in VS Code (see option (a) or (b) in "Quick start" above).
    Verifying the formalization requires checking two aspects.  The instructions below ensure that these are met:
      - that the formalization builds without errors and does not use any escape hatches like `sorry`, as well as
      - that the top-level definitions and theorem statements match the paper.

  2. Check that the formalization successfully builds by running this command (you can use the integrated terminal in VS Code for this):
```shell
lake build
```
  The build is successful if you don't see any error messages.

  3. Check that the formalization does not contain `sorry` or `axiom` by using the search function of VS Code.

  4. The definition of extended regular expressions (ERE) from Section 2.5 corresponds to the inductive type `ERE` in the file `Regex/Definitions.lean`.  Check that the constructors and the notation matches the paper.

  5. The definition of RLTL from Section 7.3 corresponds to the inductive type `RLTL` in the file `Regex/Definitions.lean`.  Check that the constructors and the notation matches the paper.  Note that we append the subscript ₗ to some of the operators to prevent clashes with Lean syntax.

  6. The definition of ⊧ for EREs from Section 6.1 corresponds to the definition `ERE.models` in the file `Regex/EREMatchSemantics.lean`.

  7. The definition of ERE derivatives from Section 7.1 corresponds to the definition `ERE.derivative` in the file `Regex/EREMatchSemantics.lean`.  Check that these match; note that the `lift_*`, `pure` and `Pred` functions are left implicit in the paper for brevity.

  8. The definition of OneStep from Section 7.2 corresponds to the definition `OneStep` in the file `Regex/RLTL.lean`.  Convince yourself that it is the same as in the paper.

  9. The Lean definition `InOmegaLanguage` in the file `Regex/OmegaLanguage.lean` is described in Section 7.6.  The notation `w ∈* R` expresses that a stream `w` matches the language of `R^*`.

  10. The definition of ⊧ for RLTL from Section 7.3 corresponds to the definition `RLTL.models` in the file `Regex/RLTL.lean`.  Convince yourself that it is the same as in the paper.

  11. The definition of RLTL derivatives from Section 7.5 corresponds to the definition `RLTL.derivative` in the file `Regex/RLTL.lean`.  Check that these match; note that the `lift_*`, `pure` and `Pred` functions are left implicit in the paper for brevity.

  12. Theorem 4 from Section 7.5 corresponds to the theorem `derivation` at the end of the file `Regex/RLTL.lean`.  Check that the statement matches.  As explained in Section 7.6, the EBA is implemented in Lean as a type class.  The assumption on the EBA is introduced at the begining of the file with a `variable` command.  Hover over the `derivation` identifier in VS Code to see the full type, including the type class.

  13. Check that the theorem `derivation` does not use any nonstandard axioms by appending this line to the end of the file `Regex/RLTL.lean`:
```lean
#print axioms derivation
```
  This command generates an informational message listing the axioms that are transitively used by our formalization.  (VS Code checks the file as you type, you will get blue squigglies a moment after you insert the line.)  All of these are standard built-in axioms provided by Lean:
```
'derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Dependencies

 - [Lean](https://lean-lang.org/) 4.7.0
 - [mathlib](https://github.com/leanprover-community/mathlib4/) revision [a5485f37](https://github.com/leanprover-community/mathlib4/tree/a5485f370ebd36f0c873820b1717d3d03b43b35e) from April 21 2024

The Lean version manager elan and the build tool lake will automatically download these dependency versions when you run `lake build`.

Lean has minimal platform requirements.  The instructions provided above will work on Ubuntu 24.04 (x86-64) with git and curl installed.  Other platforms, including Windows and macOS, are supported by Lean as well.  Please see the [Lean documentation](https://lean-lang.org/lean4/doc/setup.html) for more details on platform support.
