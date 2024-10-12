import Mathlib.Tactic.Linarith
import Mathlib.Data.Prod.Lex
import Mathlib.Order.BooleanAlgebra

/-!
# Main definitions

Contains the definition of effective boolean algebras, regular expressions, and RLTL formulas.
-/

/-- Denotation typeclass, used to equip a boolean algebra with a denotation function. -/
class Denotation (α : Type u) (σ : outParam (Type v)) where
  denote : α → σ → Bool
export Denotation (denote)

/-- Effective boolean algebra typeclass, with laws. -/
class EffectiveBooleanAlgebra (α : Type u) (σ : outParam (Type v))
    extends Denotation α σ, Bot α, Top α, Inf α, Sup α, HasCompl α where
  denote_bot : denote ⊥ c = false
  denote_top : denote ⊤ c = true
  denote_compl : denote aᶜ c = !denote a c
  denote_inf : denote (a ⊓ b) c = (denote a c && denote b c)
  denote_sup : denote (a ⊔ b) c = (denote a c || denote b c)

open EffectiveBooleanAlgebra in
attribute [simp] denote_bot denote_top denote_inf denote_sup denote_compl

/-- Freely generated boolean algebra on a set of predicates. -/
inductive BA (α : Type u)
  | atom (a : α)
  | top | bot
  | and (a b : BA α)
  | or (a b : BA α)
  | not (a : BA α)
  deriving Repr, DecidableEq
open BA

/-- Denotation function induced on the free boolean algebra. -/
protected def BA.denote [Denotation α σ] (c : σ) : BA α → Bool
  | atom a => denote a c
  | not a => !(a.denote c)
  | and a b => a.denote c && b.denote c
  | or a b => a.denote c || b.denote c
  | bot => false
  | top => true

/-- The free boolean algebra is indeed an effective boolean algebra. -/
instance [Denotation α σ] : EffectiveBooleanAlgebra (BA α) σ where
  bot := BA.bot
  top := BA.top
  inf := BA.and
  sup := BA.or
  compl := BA.not
  denote_bot := rfl
  denote_top := rfl
  denote_inf := rfl
  denote_sup := rfl
  denote_compl := rfl
  denote a c := a.denote c

@[simp]
def modelsEBA (a : σ) (φ : α) [EffectiveBooleanAlgebra α σ] := denote φ a
infixr:40 " ⊨ " => modelsEBA

/-- The class of extended regular expressions (ERE) which includes
    intersection and negation. -/
inductive ERE (α : Type) where
  | ε                 : ERE α
  | Pred (e : α)      : ERE α
  | Alternation       : ERE α → ERE α → ERE α
  | Intersection      : ERE α → ERE α → ERE α
  | Concatenation     : ERE α → ERE α → ERE α
  | Star              : ERE α → ERE α
  | Negation          : ERE α → ERE α
  deriving Repr, DecidableEq
open ERE

infixr:35 " ⋓ "  => Alternation
infixr:40 " ⋒ "  => Intersection
infixr:50 " ⬝ "  => Concatenation
postfix:max "*"  => Star
prefix:max "~"   => Negation

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
  | ESI : ERE α → RLTL α → RLTL α      -- existential suffix implication
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
infixr:20 " ◇→ " => RLTL.ESI
infixr:20 " ▫→ " => RLTL.USI
infixr:45 " →ₗ " => RLTL.Implication
prefix:max "¬ₗ"  => RLTL.Neg
notation "⦃" r "⦄"  => RLTL.WeakClosure r
notation "!⦃" r "⦄" => RLTL.Neg (WeakClosure r)
