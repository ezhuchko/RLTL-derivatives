import Regex.Ere.Derivative
import Regex.Rltl.Definitions
import Mathlib.Data.Stream.Defs

/-!
# RLTL derivatives

Contains the derivation rules for RLTL: the symbolic derivative `𝜕 φ` and the multi-step
evaluation function.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' TTerm Ere RLTL EffectiveBooleanAlgebra
open scoped Models

/-- OneStep of r is a predicate which looks one derivative step ahead. -/
def OneStep (r : Ere α) : α := OneStep' (derivative r)

/-- The derivatives of RLTL are defined using transition terms, `TTerm⟨α,RLTL α⟩`, where
    `α` is the type of alphabet and `RLTL α` is the type of leaves. -/
@[simp]
def RLTL.derivative (r : RLTL α) : TTerm α (RLTL α) :=
  match r with
  | .Pred a => node a (.leaf (Pred ⊤)) (.leaf (Pred ⊥))
  | ¬ₗ φ    => liftUnary (¬ₗ ·) (derivative φ)
  | φ ∧ₗ ψ  => liftBinary (· ∧ₗ ·) (derivative φ) (derivative ψ)
  | φ ∨ₗ ψ  => liftBinary (· ∨ₗ ·) (derivative φ) (derivative ψ)
  | X φ     => .leaf φ
  | φ U ψ   =>
    let rhs := liftBinary (· ∧ₗ ·) (derivative φ) (.leaf (φ U ψ))
    liftBinary (· ∨ₗ ·) (derivative ψ) rhs
  | φ R ψ   =>
    let rhs := liftBinary (· ∨ₗ ·) (derivative φ) (.leaf (φ R ψ))
    liftBinary (· ∧ₗ ·) (derivative ψ) rhs
  | φ →ₗ ψ  => liftBinary (· →ₗ ·) (derivative φ) (derivative ψ)
  | r ∷ φ  =>
    let lhs := node (OneStep r) (derivative φ) (.leaf (Pred ⊥))
    liftBinary (· ∨ₗ ·) lhs (liftUnary (· ∷ φ) (δ r))
  | r :> φ  =>
    let lhs := node (OneStep r) (derivative φ) (.leaf (Pred ⊤))
    liftBinary (· ∧ₗ ·) lhs (liftUnary (· :> φ) (δ r))
  | ⦃ r ⦄   =>
    if nullable r then
      .leaf (Pred ⊤)
    else
      liftUnary (⦃ · ⦄) (δ r)
  | r^ω     =>
    let lhs := liftBinary (· ∧ₗ ·) (derivative (Pred (OneStep r)))
                                    (.leaf r^ω)
    liftBinary (· ∨ₗ ·) lhs (liftUnary (· ∷ X (r^ω)) (δ r))
termination_by sizeOf_RLTL r
namespace RLTL
scoped prefix:max " 𝜕 " => RLTL.derivative
end RLTL

/-- Multi-step evaluation function. -/
def RLTL.multi_step : RLTL α → List σ → Stream' σ → RLTL α
  | φ, [], _ => φ
  | φ, .cons a as, w => multi_step ((𝜕 φ)[a]) as w
