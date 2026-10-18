import SymbolicEquivalence.TransitionTerm
import Regex.Ere.Definitions

open Ere TTerm
open scoped Models

/-!
# Symbolic derivatives

Contains the nullability check and the symbolic derivative `δ r : TTerm α (Ere α)`, together
with the multi-step evaluation function.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-- The `nullable` function checks if the language of a given regex contains the empty
    string i.e. `ε ∈ L(r) ?`. -/
@[simp]
def nullable : Ere α → Bool
  | ε      => true
  | Pred _ => false
  | l ⋓ r  => nullable l || nullable r
  | l ⋒ r  => nullable l && nullable r
  | l ⬝ r  => nullable l && nullable r
  | _ *    => true
  | ~ r    => !nullable r
  | _ : _  => false

/-- The predicate satisfied by exactly the characters that lead to a nullable leaf. -/
@[simp]
def OneStep' : TTerm α (Ere α) → α
  | leaf r     => if nullable r then ⊤ else ⊥
  | node α f g => (α ⊓ OneStep' f) ⊔ (αᶜ ⊓ OneStep' g)

@[simp]
def Ere.derivative : Ere α → TTerm α (Ere α)
  | ε      => leaf (Pred ⊥)
  | Pred b => node b (leaf ε) (leaf (Pred ⊥))
  | l ⋓ r  => liftBinary (· ⋓ ·) (derivative l) (derivative r)
  | l ⋒ r  => liftBinary (· ⋒ ·) (derivative l) (derivative r)
  | l ⬝ r  =>
    if nullable l then
      liftBinary (· ⋓ ·) (liftBinary (· ⬝ ·) (derivative l) (leaf r)) (derivative r)
    else
      liftBinary (· ⬝ ·) (derivative l) (leaf r)
  | r *    => liftBinary (· ⬝ ·) (derivative r) (leaf r*)
  | ~ r    => liftUnary (~ ·) (derivative r)
  | l : r  =>
    let lhs := node (OneStep' (derivative l)) (derivative r) (leaf (Pred ⊥))
    liftBinary (· ⋓ ·) lhs (liftUnary (· : r) (derivative l))

prefix:max " δ " => Ere.derivative

/-- Multi-step evaluation function. -/
@[simp]
def Ere.multi_step : Ere α → List σ → Ere α
  | r, []      => r
  | r, a :: as => multi_step ((δ r)[a]) as
