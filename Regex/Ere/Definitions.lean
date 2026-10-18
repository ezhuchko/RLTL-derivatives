
/-!
# Main definitions

Contains the definition of extended regular expressions with fusion.
-/

/-- The class of extended regular expressions (ERE) which includes
    intersection, negation, and fusion. The fusion operator `l : r` encodes
    an overlap such that the last letter matching `l` is the first letter
    matching `r`. -/
inductive Ere (α : Type) where
  | ε : Ere α
  | Pred (e : α) : Ere α
  | Alternation : Ere α → Ere α → Ere α
  | Intersection : Ere α → Ere α → Ere α
  | Concatenation : Ere α → Ere α → Ere α
  | Star : Ere α → Ere α
  | Negation : Ere α → Ere α
  | Fusion : Ere α → Ere α → Ere α
  deriving Repr, DecidableEq
open Ere

infixr:35 " ⋓ "  => Alternation
infixr:40 " ⋒ "  => Intersection
infixr:50 " ⬝ "  => Concatenation
postfix:max "*"  => Ere.Star
prefix:max "~"   => Negation
infixr:40 " : "  => Fusion

/-- Encoding of Star using bounded loops. -/
@[simp]
def Ere.repeatCat (R : Ere α) (n : Nat) : Ere α :=
  match n with
  | 0          => ε
  | Nat.succ n => R ⬝ (repeatCat R n)

notation f "⁽" n "⁾" => repeatCat f n
