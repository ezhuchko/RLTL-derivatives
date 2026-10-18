import Regex.Rltl.Semantics
import Regex.Rltl.Derivatives
import Regex.Ere.Correctness

/-!
# Correctness of RLTL derivatives

Contains the main derivation theorem: `a :: w |= φ ↔ w |= (𝜕 φ)[a]`.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' TTerm Ere RLTL EffectiveBooleanAlgebra
open scoped Models

theorem modelsOneStep {r : Ere α} {a : σ} : [] ⊫ (δ r)[a] ↔ a ⊨ OneStep r := denoteOneStep

/-- A one-letter word matches `r` iff the letter satisfies `OneStep r`. -/
theorem singleton_models_iff {r : Ere α} {a : σ} : [a] ⊫ r ↔ a ⊨ OneStep r :=
  Ere.derivation.trans modelsOneStep

/-! ### The cases of the main theorem that need more than unfolding -/

section Cases

variable {ψ : RLTL α} {r : Ere α} {a : σ} {w : Stream' σ}

/-- `r ∷ ψ`: either the first match of `r` is just `[a]` and `ψ` must hold from `a` on,
    or the match of `r` continues past `a`. -/
theorem derivation_esi (ih : ∀ {a : σ} {w : Stream' σ}, a :: w |= ψ ↔ w |= (𝜕 ψ)[a]) :
    a :: w |= (r ∷ ψ) ↔ w |= (𝜕 (r ∷ ψ))[a] := by
  rw [models_esi, ← Nat.or_exists_add_one]
  by_cases g : a ⊨ OneStep r <;>
    simp [g, models_esi, Stream'.take_zero, drop_succ, Stream'.tail_cons,
      modelsOneStep, Ere.derivation, ih]

/-- `r :> ψ`: dual to `derivation_esi`. -/
theorem derivation_usi (ih : ∀ {a : σ} {w : Stream' σ}, a :: w |= ψ ↔ w |= (𝜕 ψ)[a]) :
    a :: w |= (r :> ψ) ↔ w |= (𝜕 (r :> ψ))[a] := by
  rw [models_usi, ← Nat.and_forall_add_one]
  by_cases g : a ⊨ OneStep r <;>
    simp [g, models_usi, Stream'.take_zero, drop_succ, Stream'.tail_cons,
      modelsOneStep, Ere.derivation, ih]

/-- `⦃ r ⦄`: if `r` is nullable the formula holds trivially; otherwise some prefix of `a :: w`
    must be (the start of) a match of `r`. -/
theorem derivation_weakClosure : a :: w |= ⦃ r ⦄ ↔ w |= (𝜕 ⦃ r ⦄)[a] := by
  rw [models_weakClosure]
  by_cases g : nullable r
  · simpa [g] using .inl ⟨0, equivalenceNull.mpr g⟩
  · rw [← Nat.or_exists_add_one]
    simp only [Stream'.take_zero, equivalenceNull, g, Bool.false_eq_true,
      Stream'.take_succ_cons, Ere.derivation, false_or, gt_iff_lt, RLTL.derivative, ↓reduceIte,
      eval_liftUnary, models_weakClosure]
    refine or_congr_right ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · obtain ⟨x, hx⟩ := h (i + 1) (by omega)
      exact ⟨x, by simpa [Ere.derivation] using hx⟩
    · obtain _ | _ | i := i
      · omega
      · obtain ⟨x, hx⟩ := h 1 Nat.one_pos
        exact ⟨take 1 w ++ x, by simpa [Stream'.take_zero, Ere.derivation] using hx⟩
      · obtain ⟨x, hx⟩ := h (i + 1) (by omega)
        exact ⟨x, by simpa [Ere.derivation] using hx⟩

/-- `r^ω`: the first block of the ω-word is either `[a]` itself, or starts with `a` and
    continues into `w`. -/
theorem derivation_omegaClosure : a :: w |= r^ω ↔ w |= (𝜕 r^ω)[a] := by
  simp only [RLTL.models, RLTL.derivative, eval_liftBinary, eval_leaf, eval_node,
             eval_liftUnary, tail_drop']
  -- the first block has length 1 (`[a] ⊫ r`) or `i + 2` (`a :: take (i + 1) w ⊫ r`)
  have first : (w |= if a ⊨ OneStep r then Pred ⊤ else @RLTL.Pred α ⊥) ↔ [a] ⊫ r := by
    rw [singleton_models_iff]
    split_ifs with g <;> simp [g]
  rw [regexOmegaClosure, first]
  constructor
  · rintro ⟨_ | _ | i, hi, hr, hw⟩
    · omega
    · exact .inl ⟨hr, hw⟩
    · exact .inr ⟨i, Ere.derivation.mp hr, hw⟩
  · rintro (⟨hr, hw⟩ | ⟨i, hr, hw⟩)
    · exact ⟨1, Nat.one_pos, hr, hw⟩
    · exact ⟨i + 2, by omega, Ere.derivation.mpr hr, hw⟩

end Cases

/-- The main theorem proving correctness of the derivation rules for RLTL. -/
theorem RLTL.derivation {φ : RLTL α} {a : σ} {w : Stream' σ} :
    a :: w |= φ ↔ w |= (𝜕 φ)[a] := by
  induction φ generalizing a w with
  | Pred p => by_cases h : a ⊨ p <;> simp [h]
  | Neg φ ih => simp [ih]
  | And φ ψ ihφ ihψ | Or φ ψ ihφ ihψ | Implication φ ψ ihφ ihψ => simp [ihφ, ihψ]
  -- `X φ` steps over `a`
  | Next φ => simp [Stream'.tail_cons]
  -- `U` and `R` are unfolded once with their expansion laws
  | Until φ ψ ihφ ihψ =>
    rw [expansion_until]
    simp [Stream'.tail_cons, ihφ, ihψ]
  | Release φ ψ ihφ ihψ =>
    rw [expansion_release]
    simp [Stream'.tail_cons, ihφ, ihψ]
  | ESI r ψ ih => exact derivation_esi ih
  | USI r ψ ih => exact derivation_usi ih
  | WeakClosure r => exact derivation_weakClosure
  | OmegaClosure r => exact derivation_omegaClosure

theorem RLTL.derivationMultiStep {φ : RLTL α} {u : List σ} {w : Stream' σ} :
    appendStream' u w |= φ ↔ w |= multi_step φ u w :=
  match u with
  | [] => by simp [multi_step]
  | .cons a as => by rw [multi_step, cons_append_stream, RLTL.derivation, RLTL.derivationMultiStep]
