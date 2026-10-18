import SymbolicEquivalence.EffectiveBooleanAlgebra

/-!
# LTL syntax

This file defines linear temporal logic formulas `LTL α` over a symbolic alphabet `α`.
-/

variable {α : Type}

/-- The type of LTL formulas over predicates `α`. -/
inductive LTL (α : Type) : Type
  | Pred (a : α) : LTL α
  | Neg : LTL α → LTL α
  | And : LTL α → LTL α → LTL α
  | Or : LTL α → LTL α → LTL α
  | Next : LTL α → LTL α
  | Until : LTL α → LTL α → LTL α
  | Release : LTL α → LTL α → LTL α
  deriving Repr, DecidableEq

namespace LTL

@[simp]
def tt [Top α] : LTL α := Pred ⊤
@[simp]
def ff [Bot α] : LTL α := Pred ⊥

scoped infixr:40 " 𝒰 "  => LTL.Until
scoped infixr:40 " ℛ "  => LTL.Release
scoped prefix:max "𝒳"   => LTL.Next
scoped infixr:35 " ∨ₗ " => LTL.Or
scoped infixr:40 " ∧ₗ " => LTL.And
scoped prefix:max "¬ₗ"  => LTL.Neg

end LTL
