import Regex.Ere.Definitions

/-!
# Main definitions

Contains the definition of RLTL formulas.
-/

/-- The combination of linear temporal logic and extended regular expressions modulo an EBA. -/
inductive RLTL (α : Type) where
  | Pred (a : α) : RLTL α
  | Neg : RLTL α → RLTL α
  | And : RLTL α → RLTL α → RLTL α
  | Or : RLTL α → RLTL α → RLTL α
  | Next : RLTL α → RLTL α
  | Until : RLTL α → RLTL α → RLTL α
  | Release : RLTL α → RLTL α → RLTL α
  | Implication : RLTL α → RLTL α → RLTL α
  | ESI : Ere α → RLTL α → RLTL α      -- 𝜔-fusion (existential suffix implication)
  | USI : Ere α → RLTL α → RLTL α      -- universal suffix implication
  | WeakClosure : Ere α → RLTL α
  | OmegaClosure : Ere α → RLTL α

namespace RLTL

scoped infixr:40 " U "  => RLTL.Until
scoped infixr:40 " R "  => RLTL.Release
scoped prefix:max " X " => RLTL.Next
scoped postfix:max "^ω " => RLTL.OmegaClosure
scoped infixr:35 " ∨ₗ " => RLTL.Or
scoped infixr:40 " ∧ₗ " => RLTL.And
scoped infixr:20 " ∷ " => RLTL.ESI
scoped infixr:20 " :> " => RLTL.USI
scoped infixr:45 " →ₗ " => RLTL.Implication
scoped prefix:max "¬ₗ"  => RLTL.Neg
scoped notation "⦃" r "⦄"  => RLTL.WeakClosure r
scoped notation "!⦃" r "⦄" => RLTL.Neg (RLTL.WeakClosure r)

end RLTL

open Ere RLTL

/-- The termination metric is needed to show the well-foundedness of the
    `derivative` function. -/
@[simp]
def sizeOf_RLTL : RLTL α → Nat
  | RLTL.Pred _    => 0
  | ¬ₗ φ           => 1 + sizeOf_RLTL φ
  | φ ∧ₗ ψ         => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | φ ∨ₗ ψ         => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | φ →ₗ ψ         => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | X φ            => 1 + sizeOf_RLTL φ
  | φ U ψ          => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | φ R ψ          => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | _ ∷ φ          => 1 + sizeOf_RLTL φ
  | _ :> φ         => 1 + sizeOf_RLTL φ
  | ⦃ _ ⦄          => 1
  | OmegaClosure _ => 1
