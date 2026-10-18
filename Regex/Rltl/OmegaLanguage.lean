import Regex.Rltl.Definitions
import Regex.Ere.Semantics
import Mathlib.Data.Stream.Init
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Omega language

Contains the specification of omega languages.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' Ere RLTL

/-- The starting index of the `i`-th subword, given a stream of subword lengths-minus-one
    `w`: it is the sum of the (`+1`-corrected) lengths of the preceding `i` subwords. -/
def getWordStart (w : Stream' ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, (w.get j + 1)

@[simp]
theorem getWordStart_zero (w : Stream' ℕ) : getWordStart w 0 = 0 := by
  simp [getWordStart]

theorem getWordStart_succ (w : Stream' ℕ) (i : ℕ) :
    getWordStart w (i + 1) = (w.head + 1) + getWordStart w.tail i := by
  rw [Nat.add_comm (w.head + 1)]
  simp only [getWordStart, Finset.sum_range_succ', Stream'.get_tail]

/-- This predicate checks whether a stream `w` is in the ω-closure of `r`, based on a
    stream of subword lengths `deltas`. -/
@[simp]
def IsDeltasOmegaLanguage (w : Stream' σ) (r : Ere α) (deltas : Stream' ℕ) : Prop :=
  ∀ (i : ℕ),                            -- for all starting indices (of all subwords)
    let start := getWordStart deltas i  -- get the starting index of the subword
    let len := get deltas i + 1         -- get the length of the subword
    take len (drop start w) ⊫ r         -- check that it is in the language of r

/-- This predicate checks whether a stream `w` is in the ω-closure of `r`, i.e. `w ∈ L(r)^ω`.
    The idea is to show the existence of a stream of natural numbers `deltas`, which
    partitions `w` into subwords of non-zero lengths that are each in the language
    of `r`. The stream `deltas` ensures that the partitioning is well-defined. -/
def InOmegaLanguage (w : Stream' σ) (r : Ere α) : Prop :=
  ∃ (deltas : Stream' ℕ), IsDeltasOmegaLanguage w r deltas

namespace RLTL
scoped infixr:40 " ∈* "  => InOmegaLanguage
end RLTL

theorem charOmegaDrop {w : Stream' σ} {r : Ere α} {deltas : Stream' ℕ}
    (h : IsDeltasOmegaLanguage w r deltas) :
    IsDeltasOmegaLanguage (drop (head deltas + 1) w) r (tail deltas) := fun i => by
  dsimp only
  rw [Stream'.drop_drop, ← getWordStart_succ]
  exact h (i + 1)

theorem charOmegaHead {w : Stream' σ} {r : Ere α} {deltas : Stream' ℕ}
    (h : IsDeltasOmegaLanguage w r deltas) :
    take ((head deltas) + 1) w ⊫ r := h 0

theorem charOmegaCons {w : Stream' σ} {r : Ere α} {deltas : Stream' ℕ} {a : σ} {str : List σ}
    (h : IsDeltasOmegaLanguage w r deltas) (m : a :: str ⊫ r) :
    -- we just put str and not a :: str because in the stream the length is minus one
    IsDeltasOmegaLanguage ((a :: str) ++ₛ w) r (length str :: deltas)
  | 0 => by
    dsimp only
    rw [get_zero_cons, getWordStart_zero, Stream'.drop_zero,
      ← length_cons (a := a), Stream'.take_append_of_le_length _ _ _ le_rfl, List.take_length]
    exact m
  | i + 1 => by
    dsimp only
    rw [getWordStart_succ, ← Stream'.drop_drop, Stream'.head_cons,
      ← length_cons (a := a), drop_append_stream]
    exact h i

theorem regexOmegaClosure {r : Ere α} :
    w ∈* r ↔ ∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r := by
  constructor
  · rintro ⟨deltas, h⟩
    exact ⟨head deltas + 1, Nat.succ_pos _, charOmegaHead h, tail deltas, charOmegaDrop h⟩
  · rintro ⟨_ | i, hi, h1, deltas, h⟩
    · omega
    refine ⟨i :: deltas, fun | 0 => h1 | j + 1 => ?_⟩
    dsimp only
    rw [getWordStart_succ, ← Stream'.drop_drop]
    exact h j
