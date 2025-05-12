import Regex.TTerm
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init

/-!
# LTL derivation

Contains match semantics and derivation rules for LTL, as well as the main
derivation theorem.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' TTerm

inductive LTL (α : Type) where
  | Pred (a : α) : LTL α
  | Neg : LTL α → LTL α
  | And : LTL α → LTL α → LTL α
  | Or : LTL α → LTL α → LTL α
  | Next : LTL α → LTL α
  | Until : LTL α → LTL α → LTL α
  | Release : LTL α → LTL α → LTL α
  | Implication : LTL α → LTL α → LTL α
open LTL

infixr:40 " U "  => Until
infixr:40 " R "  => Release
prefix:max " X " => Next
infixr:35 " ∨ₗ " => LTL.Or
infixr:40 " ∧ₗ " => LTL.And
prefix:max "¬ₗ"  => LTL.Neg
infixr:30 " →ₗ " => LTL.Implication

/-- The derivatives of LTL are defined using transition terms, `TTerm⟨α,LTL α⟩`, where
    `α` is the type of alphabet and `LTL α` is the type of leaves. -/
@[simp]
def LTL.derivative : LTL α → TTerm α (LTL α)
  | .Pred a => Node a (.pure (.Pred ⊤)) (.pure (.Pred ⊥))
  | ¬ₗ φ    => lift_unary (¬ₗ ·) (derivative φ)
  | φ ∧ₗ ψ  => lift_binary (· ∧ₗ ·) (derivative φ) (derivative ψ)
  | φ ∨ₗ ψ  => lift_binary (· ∨ₗ ·) (derivative φ) (derivative ψ)
  | X φ     => .pure φ
  | φ U ψ   =>
    let rhs := lift_binary (· ∧ₗ ·) (derivative φ) (.pure (φ U ψ))
    lift_binary (· ∨ₗ ·) (derivative ψ) rhs
  | φ R ψ   =>
    let rhs := lift_binary (· ∨ₗ ·) (derivative φ) (.pure (φ R ψ))
    lift_binary (· ∧ₗ ·) (derivative ψ) rhs
  | φ →ₗ ψ  => lift_binary (· →ₗ ·) (derivative φ) (derivative ψ)
