import Regex.ERE
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool
import Batteries.Data.Nat.Lemmas

/-!
# Omega language

Contains the specification of omega languages.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' TTerm ERE RLTL

/-- This predicate checks whether a stream `w` is in the ω-closure of `r` i.e. `w ∈ r*?`.
    The idea is to show the existence of a stream of natural numbers `deltas`, which
    partitions `w` into subwords of non-zero lengths that are each in the language
    of `r`. The stream `deltas` ensures that the partitioning is well-defined. -/
structure InOmegaLanguage (w : Stream' σ) (r : ERE α) : Prop where
  ind : ∀ (i : ℕ), Stream'.take (i + 1) w ⊫ r*
      → ∃ j, Stream'.take (j + 1) (Stream'.drop (i + 1) w) ⊫ r
  base : ∃ l : ℕ, Stream'.take (l + 1) w ⊫ r

infixr:40 " ∈* "  => InOmegaLanguage

theorem take_length_append : Stream'.take (length s) (s ++ₛ w) = s := by
  match s with
  | [] => simp only [length_nil, Stream'.take_zero]
  | .cons a s =>
    erw[Stream'.take_succ,Stream'.cons_append_stream]
    simp only [get_zero_cons, Stream'.tail_cons, cons.injEq, true_and]
    exact take_length_append

theorem append_stream {r : ERE α} (left : ws ⊫ r) (right : w ∈* r) :
  ws ++ₛ w ∈* r := by
  sorry
  --have := right (i - ws.length)
  -- use left and hi
  --sorry

theorem split_stream {r : ERE α} (h : ws ++ₛ w ∈* r) (left : ws ⊫ r):
  w ∈* r := by
  constructor
  . intro i hi
    have := h.ind (i + ws.length)
    have := this (by
      simp[Stream'.take]
      simp[ERE.models] at hi
      let ⟨m, p⟩ := hi
      exists m + 1
      dsimp
      unfold ERE.models
      exists ws
      exists Stream'.take (i + 1) w
      dsimp
      exists left
      exists p
      match ws with
      | [] => simp[Stream'.take_succ]
      | .cons w' ws =>
        simp[Stream'.take_succ]
        rw[Nat.add_comm]
        rw[Stream'.cons_append_stream]
        rw[Stream'.tail_cons]
        rw[Stream'.take_add]
        rw[Stream'.drop_succ]
        simp only [drop_tail']
        rw[Stream'.take_add]
        simp [take_length_append]
        rw[Stream'.drop_append_stream]
        rw[←Stream'.drop_drop]
        rw[Stream'.drop_append_stream]
        rw[Stream'.tail_eq_drop]
        unfold Stream'.take
        simp)
    rw[Nat.add_right_comm] at this
    rw[Nat.add_comm] at this
    rw[←Stream'.drop_drop] at this
    rw[Stream'.drop_append_stream] at this
    exact this
  . match ws with
    | [] => exact h.base
    | .cons w ws =>
      have := h.ind ws.length
        (by rw[←length_cons]
            rw[take_length_append (s := w :: ws)]
            simp
            exists 1
            simp
            exact left)
      rw[←length_cons] at this
      rw[Stream'.drop_append_stream] at this
      exact this

theorem regexOmegaClosure {r : ERE α} :
  w ∈* r ↔ (∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r) := by
  sorry
  -- ⟨fun ⟨deltas, h⟩ =>
  --  ⟨head deltas + 1,
  --   by simp only [gt_iff_lt, add_pos_iff, zero_lt_one, or_true],
  --   charOmegaHead h,⟨Stream'.tail deltas,charOmegaDrop h⟩⟩,
  --  fun ⟨i,hi,h1,⟨deltas,h⟩⟩ =>
  --  match i with
  --  | 0 => by simp only [gt_iff_lt, lt_self_iff_false] at hi
  --  | Nat.succ i => by
  --    exists i::deltas
  --    intro j
  --    match j with
  --    | 0 => simp only [get_zero_cons, getWordStart, Stream'.drop_zero]; exact h1
  --    | Nat.succ j =>
  --      simp only [get_succ_cons, getWordStart, Stream'.tail_cons, get_zero_cons]
  --      have := h j
  --      simp only [Stream'.drop_drop] at this
  --      rw[←Nat.succ_eq_add_one] at this; exact this⟩
