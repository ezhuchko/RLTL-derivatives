import Regex.Ere.Semantics
import Regex.Ere.Derivative

/-!
# Main correctness theorem

Contains each lemma required to show that the symbolic derivative is correct with respect to
the match semantics: `a :: xs ⊫ r ↔ xs ⊫ (δ r)[a]`.
-/

open List TTerm Ere EffectiveBooleanAlgebra
open scoped Models

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-! ### Nullability -/

theorem equivalenceNull {r : Ere α} : [] ⊫ r ↔ nullable r :=
  match r with
  | ε => by simp
  | Pred p => by simp
  | l ⋓ r => by simp [equivalenceNull (r := l), equivalenceNull (r := r)]
  | l ⋒ r => by simp [equivalenceNull (r := l), equivalenceNull (r := r)]
  | l ⬝ r => by simp [equivalenceNull (r := l), equivalenceNull (r := r)]
  | r * => iff_of_true (by simp only [Ere.models]; exact ⟨0, by simp⟩) rfl
  | ~ r => by simp [equivalenceNull (r := r)]
  | l : r => by simp

theorem denoteOneStep' {f : TTerm α (Ere α)} {a : σ} : [] ⊫ f[a] ↔ a ⊨ OneStep' f :=
  match f with
  | leaf r => by by_cases h : nullable r <;> simp [h, equivalenceNull]
  | node p f g => by
    by_cases h : a ⊨ p <;> simp [h, denoteOneStep' (f := f), denoteOneStep' (f := g)]

theorem denoteOneStep {r : Ere α} {a : σ} : [] ⊫ (δ r)[a] ↔ a ⊨ OneStep' (δ r) :=
  denoteOneStep'

/-! ### Non-empty words -/

/-- A nonempty word matches `l ⬝ r` iff its head is consumed by `l`, or `l` is skipped. -/
theorem cons_models_cat {a : σ} {xs : List σ} {l r : Ere α} :
    a :: xs ⊫ (l ⬝ r) ↔
      (∃ u, a :: u ⊫ l ∧ ∃ v, v ⊫ r ∧ u ++ v = xs) ∨ ([] ⊫ l ∧ a :: xs ⊫ r) := by
  simp only [Ere.models, append_eq_cons_iff]
  constructor
  · rintro ⟨u, v, hu, hv, ⟨rfl, rfl⟩ | ⟨u', rfl, rfl⟩⟩
    · exact .inr ⟨hu, hv⟩
    · exact .inl ⟨u', hu, v, hv, rfl⟩
  · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨hl, hr⟩)
    · exact ⟨a :: u, v, hu, hv, .inr ⟨u, rfl, rfl⟩⟩
    · exact ⟨[], a :: xs, hl, hr, .inl ⟨rfl, rfl⟩⟩

theorem models_star {xs : List σ} {r : Ere α} : xs ⊫ (r *) ↔ ∃ m, xs ⊫ (r ⁽ m ⁾) := by
  simp only [Ere.models]

/-- A nonempty word matches `r*` iff a nonempty prefix matches `r` and the rest matches `r*`. -/
theorem cons_models_star {a : σ} {xs : List σ} {r : Ere α} :
    a :: xs ⊫ (r *) ↔ ∃ u, a :: u ⊫ r ∧ ∃ v, v ⊫ (r *) ∧ u ++ v = xs := by
  rw [models_star]
  constructor
  · rintro ⟨n, h⟩
    induction n with
    | zero => simp at h
    | succ n ih =>
      obtain ⟨u, hu, v, hv, rfl⟩ | ⟨-, h⟩ := cons_models_cat.mp h
      · exact ⟨u, hu, v, models_star.mpr ⟨n, hv⟩, rfl⟩
      · exact ih h
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨n, hv⟩ := models_star.mp hv
    exact ⟨n + 1, cons_models_cat.mpr (.inl ⟨u, hu, v, hv, rfl⟩)⟩

/-- A nonempty word matches `l : r` iff `l` matches just its head and `r` the whole word, or the
    head is consumed by `l` before the overlapping letter. -/
theorem cons_models_fusion {a : σ} {xs : List σ} {l r : Ere α} :
    a :: xs ⊫ (l : r) ↔
      ([a] ⊫ l ∧ a :: xs ⊫ r) ∨ ∃ u v c, a :: (u ++ [c]) ⊫ l ∧ c :: v ⊫ r ∧ u ++ c :: v = xs := by
  simp only [Ere.models]
  constructor
  · rintro ⟨_ | ⟨b, u⟩, v, c, hl, hr, he⟩ <;> simp at he
    · obtain ⟨rfl, rfl⟩ := he; exact .inl ⟨hl, hr⟩
    · obtain ⟨rfl, rfl⟩ := he; exact .inr ⟨u, v, c, hl, hr, rfl⟩
  · rintro (⟨hl, hr⟩ | ⟨u, v, c, hl, hr, rfl⟩)
    · exact ⟨[], xs, a, hl, hr, rfl⟩
    · exact ⟨a :: u, v, c, hl, hr, by simp⟩

/-! ### Correctness of the symbolic derivative -/

/-- The symbolic derivative is correct: `a :: xs ⊫ r` iff `xs` matches the derivative at `a`. -/
theorem Ere.derivation {r : Ere α} {a : σ} {xs : List σ} : a :: xs ⊫ r ↔ xs ⊫ (δ r)[a] :=
  match r with
  | ε => by simp
  | Pred p => by by_cases h : a ⊨ p <;> simp [h]
  | l ⋓ r => by simp [Ere.derivation (r := l), Ere.derivation (r := r)]
  | l ⋒ r => by simp [Ere.derivation (r := l), Ere.derivation (r := r)]
  | ~ r => by simp [Ere.derivation (r := r)]
  | r * => by rw [cons_models_star]; simp [Ere.derivation (r := r)]
  | l ⬝ r => by
    rw [cons_models_cat]
    by_cases g : nullable l <;>
      simp [g, equivalenceNull, Ere.derivation (r := l), Ere.derivation (r := r)]
  | l : r => by
    rw [cons_models_fusion]
    by_cases g : a ⊨ OneStep' (δ l) <;>
      simp [g, denoteOneStep, Ere.derivation (r := l), Ere.derivation (r := r)]

theorem Ere.derivationMultiStep {r : Ere α} {u v : List σ} :
    v ⊫ multi_step r u ↔ u ++ v ⊫ r :=
  match u with
  | [] => .rfl
  | a :: as => by rw [multi_step, cons_append, Ere.derivation, derivationMultiStep]
