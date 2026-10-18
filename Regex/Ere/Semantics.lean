import SymbolicEquivalence.EffectiveBooleanAlgebra
import Regex.Ere.Metrics

open Ere
open scoped Models

/-!
# Match semantics

Contains the specification of the matching relation, which follows the approach
of language-based matching.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

@[simp]
def Ere.models (xs : List σ) (r : Ere α) : Prop :=
  match r with
  | ε      => xs = []
  | Pred p => ∃ c, xs = [c] ∧ c ⊨ p
  | l ⋓ r  =>
    have : starMetric l < starMetric (l ⋓ r) := starMetric_Alt_l
    have : starMetric r < starMetric (l ⋓ r) := starMetric_Alt_r
    Ere.models xs l ∨ Ere.models xs r
  | l ⋒ r  =>
    have : starMetric l < starMetric (l ⋒ r) := starMetric_Inter_l
    have : starMetric r < starMetric (l ⋒ r) := starMetric_Inter_r
    Ere.models xs l ∧ Ere.models xs r
  | l ⬝ r  =>
    ∃ u₁ u₂,
        have : starMetric l < starMetric (l ⬝ r) := starMetric_Cat_l
        have : starMetric r < starMetric (l ⬝ r) := starMetric_Cat_r
        Ere.models u₁ l
      ∧ Ere.models u₂ r
      ∧ u₁ ++ u₂ = xs
  | r *    =>
    ∃ (m : ℕ),
    have : starMetric (r ⁽ m ⁾) < starMetric (r *) := starMetric_repeat
    Ere.models xs (r ⁽ m ⁾)
  | ~ r    =>
    have : starMetric r < starMetric (~ r) := starMetric_Negation
    ¬ Ere.models xs r
  -- fusion: the last letter matching `l` is the first letter matching `r`
  | l : r  =>
    ∃ u₁ u₂ c,
        have : starMetric l < starMetric (l : r) := starMetric_Fusion_l
        have : starMetric r < starMetric (l : r) := starMetric_Fusion_r
        Ere.models (u₁ ++ [c]) l
      ∧ Ere.models (c :: u₂) r
      ∧ u₁ ++ [c] ++ u₂ = xs
termination_by starMetric r
decreasing_by
  simp_wf; repeat assumption

notation:52 lhs:53 " ⊫ " rhs:53 => Ere.models lhs rhs
