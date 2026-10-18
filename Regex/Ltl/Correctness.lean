import Regex.Ltl.Semantics
import Regex.Ltl.Derivative
import Mathlib.Data.Stream.Init

/-!
# Correctness of LTL derivatives

This file proves that the symbolic derivative is correct: `c :: w |= φ ↔ w |= (𝜕 φ)[c]`.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open Stream' TTerm LTL
open scoped Models

theorem expansion_release {w : Stream' σ} {φ ψ : LTL α} :
    w |= (φ ℛ ψ) ↔ w |= (ψ ∧ₗ (φ ∨ₗ 𝒳(φ ℛ ψ))) := by
  simp only [models_and, models_or, models_next, models_release, drop_tail']
  constructor
  · intro h
    have h0 : w |= ψ := (h 0).elim id fun ⟨_, hi, _⟩ => absurd hi (by omega)
    refine ⟨h0, or_iff_not_imp_left.mpr fun hφ j => ?_⟩
    rcases h (j + 1) with hψ | ⟨i, hi, hφi⟩
    · exact Or.inl hψ
    · -- `i ≠ 0`, since `φ` fails at position `0`
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 :=
        Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h => hφ (by simpa [h] using hφi))
      exact Or.inr ⟨i, by omega, hφi⟩
  · rintro ⟨h0, h⟩ (_ | j)
    · exact Or.inl (by simpa using h0)
    · rcases h with hφ | h
      · exact Or.inr ⟨0, by omega, by simpa using hφ⟩
      · rcases h j with hψ | ⟨i, hi, hφi⟩
        · exact Or.inl hψ
        · exact Or.inr ⟨i + 1, by omega, hφi⟩

theorem expansion_until {w : Stream' σ} {φ ψ : LTL α} :
    w |= (φ 𝒰 ψ) ↔ w |= (ψ ∨ₗ (φ ∧ₗ 𝒳(φ 𝒰 ψ))) := by
  simp only [models_and, models_or, models_next, models_until, drop_tail']
  constructor
  · rintro ⟨j, hψ, hφ⟩
    cases j with
    | zero => exact Or.inl (by simpa using hψ)
    | succ j =>
      exact Or.inr ⟨by simpa using hφ 0 (by omega), j, hψ, fun i hi => hφ (i + 1) (by omega)⟩
  · rintro (hψ | ⟨hφ0, j, hψ, hφ⟩)
    · exact ⟨0, by simpa using hψ, by omega⟩
    · refine ⟨j + 1, hψ, fun i hi => ?_⟩
      cases i with
      | zero => simpa using hφ0
      | succ i => exact hφ i (by omega)

/-- Correctness of the symbolic derivative: `c :: w` satisfies `φ` iff `w` satisfies the
    leaf of `𝜕 φ` selected by `c`. -/
theorem LTL.derivation {φ : LTL α} {c : σ} {w : Stream' σ} :
    c::w |= φ ↔ w |= ((𝜕 φ)[c]) := by
  match φ with
  | .Pred a =>
    by_cases g : c ⊨ a <;> simp [g]
  | ¬ₗ φ =>
    simp only [derivative, eval_liftUnary, models_neg, LTL.derivation (φ := φ)]
  | φ ∧ₗ ψ | φ ∨ₗ ψ =>
    simp only [derivative, eval_liftBinary, models_and, models_or,
      LTL.derivation (φ := φ), LTL.derivation (φ := ψ)]
  | 𝒳 φ =>
    simp only [derivative, eval_leaf, models_next, tail_cons]
  | φ 𝒰 ψ =>
    rw [expansion_until]
    simp only [derivative, eval_liftBinary, eval_leaf, models_and, models_or, models_next,
      tail_cons, LTL.derivation (φ := φ), LTL.derivation (φ := ψ)]
  | φ ℛ ψ =>
    rw [expansion_release]
    simp only [derivative, eval_liftBinary, eval_leaf, models_and, models_or, models_next,
      tail_cons, LTL.derivation (φ := φ), LTL.derivation (φ := ψ)]
