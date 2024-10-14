# Symbolic Automata: 𝜔-Regularity Modulo Theories

This repo contains the Lean formalization files for the paper "Symbolic Automata: 𝜔-Regularity Modulo Theories".

## Quick start

You can run this formalization online on GitHub codespaces, without installing anything:

  1. Press the comma key (<kbd>,</kbd>) to create a codespace, or just click this link: https://codespaces.new/ezhuchko/RLTL-derivatives
  2. Wait a minute or two for the codespace to be created.
  3. Open the `Regex/Regex.lean` file, which collects all modules of the formalization.

Alternatively, you can also install Lean on your machine and run the project locally:

  1. Install VS Code and then install the `lean4` extension.
  2. Open this folder in VS Code.
  3. Open the `Regex/Regex.lean` file, which collects all modules of the formalization.

## Brief file overview

Listed below is a brief description of each file of the formalization.

- `Definitions`: main definitions common to all files: EBAs, regex, RLTL.
- `EREMatchSemantics`: the standard language-based match semantics.
- `Metrics`: metrics on regular expression to show termination of theorems/definitions.
- `OmegaLanguage`: contains the specification of omega languages.
- `RLTL`: contains the main `derivation` theorem which corresponds to Theorem 4 from Section 7.6 of the paper.
- `TTerm`: main definitions and lemmas about transition terms.
