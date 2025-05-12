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
@[simp]
def InOmegaLanguage (w : Stream' σ) (r : ERE α) : Prop :=
  ∀ (i : ℕ), Stream'.take i w ⊫ r* →
    ∃ j, Stream'.take (j + 1) (Stream'.drop i w) ⊫ r

theorem base_case {r : ERE α} (h : InOmegaLanguage w r) :
  ∃ l : ℕ, Stream'.take (l + 1) w ⊫ r :=
  h 0 (by simp; exists 0; dsimp; simp)

infixr:40 " ∈* "  => InOmegaLanguage

theorem take_length_append : Stream'.take (length s) (s ++ₛ w) = s := by
  match s with
  | [] => simp only [length_nil, Stream'.take_zero]
  | .cons a s =>
    erw[Stream'.take_succ,Stream'.cons_append_stream]
    simp only [get_zero_cons, Stream'.tail_cons, cons.injEq, true_and]
    exact take_length_append

theorem split_stream {r : ERE α} (h : ws ++ₛ w ∈* r) (left : ws ⊫ r):
  w ∈* r := by
  intro i hi
  have := h (i + ws.length)
  have := this (by
    simp[Stream'.take]
    simp[ERE.models] at hi
    let ⟨m, p⟩ := hi
    exists m + 1
    dsimp
    unfold ERE.models
    exists ws
    exists Stream'.take i w
    dsimp
    exists left
    exists p
    rw[Nat.add_comm]
    simp[Stream'.take_add]
    simp[take_length_append]
    simp[Stream'.drop_append_stream])
  rw[Nat.add_comm] at this
  rw[←Stream'.drop_drop] at this
  rw[Stream'.drop_append_stream] at this
  exact this

theorem semmm {r : ERE α} (a : xs ⊫ r) (b : ys ⊫ r*) :
  xs ++ ys ⊫ r* := by
  simp at b
  let ⟨m,hm⟩ := b
  simp
  exists m + 1
  simp
  exists xs; exists a; exists ys

theorem regexOmegaClosure {r : ERE α} :
  w ∈* r ↔ (∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r) := by
  apply Iff.intro
  . intro h
    have ⟨len,m⟩ := base_case h
    exists len + 1
    exists (by simp)
    exists m
    intro i o
    rw[Stream'.drop_drop]
    exact h (len + 1 + i) (by
      rw[Stream'.take_add]
      apply semmm m o)
  . intro ⟨i+1,ig0,h1,h2⟩
    intro j m
    by_cases ip:i + 1 ≤ j
    . have := h2 (j - (i + 1)) (by
        sorry)
      rw[Stream'.drop_drop] at this
      rw[Nat.add_sub_cancel' ip] at this
      exact this
    . simp at ip
      have := h2 (j - (i + 1))  (by
        sorry)
      rw[Stream'.drop_drop] at this
      rw[Nat.add_sub_cancel'] at this
      sorry
