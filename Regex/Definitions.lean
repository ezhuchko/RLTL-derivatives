import Mathlib.Tactic.Linarith
import Mathlib.Data.Prod.Lex
import Mathlib.Order.BooleanAlgebra

/-!
# Main definitions

Contains the definition of regular expressions and RLTL formulas.
-/

/-- The class of extended regular expressions (ERE) which includes
    intersection, negation, and fusion. The fusion operator `l : r` encodes
    an overlap such that the last letter matching `l` is the first letter
    matching `r`. -/
inductive ERE (α : Type) where
  | ε                 : ERE α
  | Pred (e : α)      : ERE α
  | Alternation       : ERE α → ERE α → ERE α
  | Intersection      : ERE α → ERE α → ERE α
  | Concatenation     : ERE α → ERE α → ERE α
  | Star              : ERE α → ERE α
  | Negation          : ERE α → ERE α
  | Fusion            : ERE α → ERE α → ERE α
  deriving Repr, DecidableEq
open ERE

infixr:35 " ⋓ "  => Alternation
infixr:40 " ⋒ "  => Intersection
infixr:50 " ⬝ "  => Concatenation
postfix:max "*"  => Star
prefix:max "~"   => Negation
infixr:40 " : "  => Fusion

/-- Encoding of Star using bounded loops. -/
@[simp]
def repeat_cat (R : ERE α) (n : ℕ) : ERE α :=
  match n with
  | 0          => ε
  | Nat.succ n => Concatenation R (repeat_cat R n)

notation f "⁽" n "⁾" => repeat_cat f n

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
  | ESI : ERE α → RLTL α → RLTL α      -- 𝜔-fusion (existential suffix implication)
  | USI : ERE α → RLTL α → RLTL α      -- universal suffix implication
  | WeakClosure : ERE α → RLTL α
  | OmegaClosure : ERE α → RLTL α
open RLTL

infixr:40 " U "  => Until
infixr:40 " R "  => Release
prefix:max " X " => Next
postfix:max "^ω " => OmegaClosure
infixr:35 " ∨ₗ " => RLTL.Or
infixr:40 " ∧ₗ " => RLTL.And
infixr:20 " ﹕﹕ " => RLTL.ESI
infixr:20 " :> " => RLTL.USI
infixr:45 " →ₗ " => RLTL.Implication
prefix:max "¬ₗ"  => RLTL.Neg
notation "⦃" r "⦄"  => RLTL.WeakClosure r
notation "!⦃" r "⦄" => RLTL.Neg (WeakClosure r)
