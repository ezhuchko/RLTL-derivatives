import Regex.Ltl.Definitions
import Mathlib.Data.Stream.Defs

/-!
# LTL semantics

This file defines the satisfaction relation `w |= φ` for `LTL α` over infinite traces
`w : Stream' σ`.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open Stream' LTL
open scoped Models

-- semantics of ltl wrt an infinite trace
def LTL.models (w : Stream' σ) : LTL α → Prop
  | .Pred (a : α) => head w ⊨ a
  | ¬ₗ φ => ¬ (LTL.models w φ)
  | φ ∧ₗ ψ => LTL.models w φ ∧ LTL.models w ψ
  | φ ∨ₗ ψ => LTL.models w φ ∨ LTL.models w ψ
  | 𝒳 φ => LTL.models (drop 1 w) φ
  | φ 𝒰 ψ =>
    ∃ (j : ℕ),   LTL.models (drop j w) ψ
               ∧ ∀ i < j, LTL.models (drop i w) φ
  | φ ℛ ψ =>
    ∀ (j : ℕ),   LTL.models (drop j w) ψ
               ∨ ∃ i < j, LTL.models (drop i w) φ
namespace LTL
scoped notation:52 lhs:53 " |= " rhs:53 => LTL.models lhs rhs
end LTL

section ModelsClauses

variable {w : Stream' σ} {φ ψ : LTL α}

@[simp] theorem LTL.models_pred {a : α} : w |= Pred a ↔ head w ⊨ a := Iff.rfl
@[simp] theorem LTL.models_neg : w |= ¬ₗ φ ↔ ¬ w |= φ := Iff.rfl
@[simp] theorem LTL.models_and : w |= (φ ∧ₗ ψ) ↔ w |= φ ∧ w |= ψ := Iff.rfl
@[simp] theorem LTL.models_or : w |= (φ ∨ₗ ψ) ↔ w |= φ ∨ w |= ψ := Iff.rfl
@[simp] theorem LTL.models_next : w |= 𝒳 φ ↔ tail w |= φ := Iff.rfl

theorem LTL.models_until :
    w |= (φ 𝒰 ψ) ↔ ∃ j, drop j w |= ψ ∧ ∀ i < j, drop i w |= φ := Iff.rfl
theorem LTL.models_release :
    w |= (φ ℛ ψ) ↔ ∀ j, drop j w |= ψ ∨ ∃ i < j, drop i w |= φ := Iff.rfl

end ModelsClauses
