import SymbolicEquivalence.TransitionTerm
import Regex.Ltl.Definitions

/-!
# LTL derivatives

This file defines the symbolic derivative `𝜕 φ : TTerm α (LTL α)` of an `LTL` formula and
the classical derivative `LTL.der`, and shows that they agree.
-/

variable {α σ : Type}

open TTerm LTL
open scoped Models

@[simp]
def LTL.derivative [Top α] [Bot α] : LTL α → TTerm α (LTL α)
  | Pred a => node a (leaf tt) (leaf ff)
  | ¬ₗ φ => liftUnary (¬ₗ ·) (LTL.derivative φ)
  | φ ∧ₗ ψ => liftBinary (· ∧ₗ ·) (LTL.derivative φ) (LTL.derivative ψ)
  | φ ∨ₗ ψ => liftBinary (· ∨ₗ ·) (LTL.derivative φ) (LTL.derivative ψ)
  | 𝒳 φ => leaf φ
  | φ 𝒰 ψ =>
    have h := liftBinary (· ∧ₗ ·) (LTL.derivative φ) (leaf (φ 𝒰 ψ))
    liftBinary (· ∨ₗ ·) (LTL.derivative ψ) h
  | φ ℛ ψ =>
    have h := liftBinary (· ∨ₗ ·) (LTL.derivative φ) (leaf (φ ℛ ψ))
    liftBinary (· ∧ₗ ·) (LTL.derivative ψ) h
namespace LTL
scoped prefix:max " 𝜕 " => LTL.derivative
end LTL

@[simp]
def LTL.der [EffectiveBooleanAlgebra α σ] : LTL α → σ → LTL α
  | Pred a, b => if b ⊨ a then tt else ff
  | ¬ₗ φ, a => ¬ₗ (der φ a)
  | φ ∧ₗ ψ, a => der φ a ∧ₗ der ψ a
  | φ ∨ₗ ψ, a => der φ a ∨ₗ der ψ a
  | 𝒳 φ, _ => φ
  | φ 𝒰 ψ, a => der ψ a ∨ₗ (der φ a ∧ₗ (φ 𝒰 ψ))
  | φ ℛ ψ, a => der ψ a ∧ₗ (der φ a ∨ₗ (φ ℛ ψ))
namespace LTL
scoped prefix:max " δ " => LTL.der
end LTL

theorem LTL.equivalence [EffectiveBooleanAlgebra α σ] (r : LTL α) (x : σ) :
  der r x = (𝜕 r)[x] := by
  match r with
  | Pred a => by_cases g : x ⊨ a <;> simp [g]
  | ¬ₗ φ => simp[LTL.equivalence φ x]
  | φ ∧ₗ ψ => simp[LTL.equivalence φ x, LTL.equivalence ψ x]
  | φ ∨ₗ ψ => simp[LTL.equivalence φ x, LTL.equivalence ψ x]
  | 𝒳 φ => simp
  | φ 𝒰 ψ => simp[LTL.equivalence φ x, LTL.equivalence ψ x]
  | φ ℛ ψ => simp[LTL.equivalence φ x, LTL.equivalence ψ x]
