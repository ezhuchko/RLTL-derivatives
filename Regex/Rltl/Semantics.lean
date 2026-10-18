import Regex.Rltl.OmegaLanguage

/-!
# RLTL semantics

Contains the match semantics of RLTL, together with the expansion laws of `U` and `R`
and algebraic rewrite rules for the suffix implications.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' Ere RLTL EffectiveBooleanAlgebra
open scoped Models

/-- The semantics of RLTL are formalised using the models relation. -/
def RLTL.models (w : Stream' σ) : RLTL α → Prop
  | .Pred p => head w ⊨ p
  | ¬ₗ φ    => ¬ RLTL.models w φ
  | φ ∧ₗ ψ  => RLTL.models w φ ∧ RLTL.models w ψ
  | φ ∨ₗ ψ  => RLTL.models w φ ∨ RLTL.models w ψ
  | X φ     => RLTL.models (tail w) φ
  | φ U ψ   =>
    ∃ j, RLTL.models (drop j w) ψ ∧ ∀ i < j, RLTL.models (drop i w) φ
  | φ R ψ   =>
      (∀ i, RLTL.models (drop i w) ψ)
    ∨ (∃ j, RLTL.models (drop j w) φ ∧ ∀ k ≤ j, RLTL.models (drop k w) ψ)
  | φ →ₗ ψ  => RLTL.models w φ → RLTL.models w ψ
  | r ∷ φ  =>
    ∃ i, take (i + 1) w ⊫ r ∧ RLTL.models (drop i w) φ
  | r :> φ  =>
    ∀ i, take (i + 1) w ⊫ r → RLTL.models (drop i w) φ
  | ⦃ r ⦄   =>
    (∃ i,   take i w ⊫ r) ∨ (∀ i > 0, ∃ x, take i w ++ x ⊫ r)
  | r^ω     => w ∈* r
namespace RLTL
scoped notation:52 lhs:53 " |= " rhs:53 => RLTL.models lhs rhs
end RLTL

section ModelsClauses

variable {w : Stream' σ} {φ ψ : RLTL α} {r : Ere α}

@[simp] theorem RLTL.models_pred {p : α} : w |= RLTL.Pred p ↔ head w ⊨ p := Iff.rfl
@[simp] theorem RLTL.models_neg : w |= (¬ₗ φ) ↔ ¬ w |= φ := Iff.rfl
@[simp] theorem RLTL.models_and : w |= (φ ∧ₗ ψ) ↔ w |= φ ∧ w |= ψ := Iff.rfl
@[simp] theorem RLTL.models_or : w |= (φ ∨ₗ ψ) ↔ w |= φ ∨ w |= ψ := Iff.rfl
@[simp] theorem RLTL.models_next : w |= (X φ) ↔ tail w |= φ := Iff.rfl
@[simp] theorem RLTL.models_imp : w |= (φ →ₗ ψ) ↔ (w |= φ → w |= ψ) := Iff.rfl

theorem RLTL.models_until :
    w |= (φ U ψ) ↔ ∃ j, drop j w |= ψ ∧ ∀ i < j, drop i w |= φ := Iff.rfl
theorem RLTL.models_release :
    w |= (φ R ψ) ↔
      (∀ i, drop i w |= ψ) ∨ ∃ j, drop j w |= φ ∧ ∀ k ≤ j, drop k w |= ψ := Iff.rfl
theorem RLTL.models_esi : w |= (r ∷ φ) ↔ ∃ i, take (i + 1) w ⊫ r ∧ drop i w |= φ := Iff.rfl
theorem RLTL.models_usi : w |= (r :> φ) ↔ ∀ i, take (i + 1) w ⊫ r → drop i w |= φ := Iff.rfl
theorem RLTL.models_weakClosure :
    w |= ⦃ r ⦄ ↔ (∃ i, take i w ⊫ r) ∨ ∀ i > 0, ∃ x, take i w ++ x ⊫ r := Iff.rfl
theorem RLTL.models_omegaClosure : w |= r^ω ↔ w ∈* r := Iff.rfl

end ModelsClauses

theorem RLTL.expansion_until {φ ψ : RLTL α} :
  w |= (φ U ψ) ↔ w |= (ψ ∨ₗ (φ ∧ₗ X(φ U ψ))) := by
  simp only [RLTL.models, drop_tail']
  constructor
  · rintro ⟨_ | j, h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h2 0 (Nat.zero_lt_succ j), j, h1, fun i hi => h2 i.succ (by omega)⟩
  · rintro (h1 | ⟨h1, j, h2, h3⟩)
    · exact ⟨0, h1, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · exact ⟨j.succ, h2, fun | 0, _ => h1 | i + 1, hi => h3 i (by omega)⟩

theorem RLTL.expansion_release {φ ψ : RLTL α} :
  w |= (φ R ψ) ↔ w |= (ψ ∧ₗ (φ ∨ₗ X(φ R ψ))) := by
  simp only [RLTL.models, drop_tail']
  constructor
  · rintro (h1 | ⟨_ | j, h1, h2⟩)
    · exact ⟨h1 0, Or.inr <| Or.inl fun i => h1 i.succ⟩
    · exact ⟨h2 0 le_rfl, Or.inl h1⟩
    · exact ⟨h2 0 (Nat.zero_le _), Or.inr <| Or.inr ⟨j, h1, fun i hi => h2 i.succ (by omega)⟩⟩
  · rintro ⟨h1, h3 | h4 | ⟨_ | i, h4, h5⟩⟩
    · exact Or.inr ⟨0, h3, fun i hi => by obtain rfl := Nat.le_zero.mp hi; exact h1⟩
    · exact Or.inl fun | 0 => h1 | j + 1 => h4 j
    · exact Or.inr ⟨1, h4, fun
        | 0, _ => h1
        | k + 1, h => by obtain rfl : k = 0 := (by omega); exact h5 0 le_rfl⟩
    · exact Or.inr ⟨i + 2, h4, fun | 0, _ => h1 | k + 1, _ => h5 k (by omega)⟩

/-- The existential suffix implication operator distributes over union. -/
theorem RLTL.esi_distributivity {l r : Ere α} {φ : RLTL α} :
  w |= ((l ⋓ r) ∷ φ) ↔ w |= (l ∷ φ) ∨ w |= (r ∷ φ) := by
  simp only [RLTL.models, Ere.models]
  constructor
  · rintro ⟨i, h1 | h1, h2⟩
    · exact Or.inl ⟨i, h1, h2⟩
    · exact Or.inr ⟨i, h1, h2⟩
  · rintro (⟨i, h1, h2⟩ | ⟨i, h1, h2⟩)
    · exact ⟨i, Or.inl h1, h2⟩
    · exact ⟨i, Or.inr h1, h2⟩

/-- The universal suffix implication operator distributes over union. -/
theorem RLTL.usi_distributivity {l r : Ere α} {φ : RLTL α} :
  w |= ((l ⋓ r) :> φ) ↔ w |= (l :> φ) ∧ w |= (r :> φ) := by
  simp only [RLTL.models, Ere.models]
  constructor
  · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro h i (hi | hi)
    · exact h.1 i hi
    · exact h.2 i hi
