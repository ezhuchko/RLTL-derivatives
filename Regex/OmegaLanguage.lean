import Regex.ERE
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool

/-!
# Omega language

Contains the specification of omega languages.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' TTerm ERE RLTL

@[simp]
def getWordStart (w : Stream' ℕ) (i : ℕ) : ℕ :=
  match i with
  | 0 => 0
  | .succ i => getWordStart (tail w) i + (head w + 1)

/-- This predicate checks whether a stream `w` is in the ω-closure of `r`, based on a
    stream of subword lengths `deltas`. -/
@[simp]
def IsDeltasOmegaLanguage (w : Stream' σ) (r : ERE α) (deltas : Stream' ℕ) : Prop :=
  ∀ (i : ℕ),                            -- for all starting indices (of all subwords)
    let start := getWordStart deltas i  -- get the starting index of the subword
    let len := get deltas i + 1         -- get the length of the subword
    take len (drop start w) ⊫ r         -- check that it is in the language of r

/-- This predicate checks whether a stream `w` is in the ω-closure of `r` i.e. `w ∈ r*?`.
    The idea is to show the existence of a stream of natural numbers `deltas`, which
    partitions `w` into subwords of non-zero lengths that are each in the language
    of `r`. The stream `deltas` ensures that the partitioning is well-defined. -/
def InOmegaLanguage (w : Stream' σ) (r : ERE α) : Prop :=
  ∃ (deltas : Stream' ℕ), IsDeltasOmegaLanguage w r deltas

infixr:40 " ∈* "  => InOmegaLanguage

theorem charOmegaDrop {w : Stream' σ} {r : ERE α} {deltas : Stream' ℕ}
  (h : IsDeltasOmegaLanguage w r deltas) :
  IsDeltasOmegaLanguage (drop (head deltas + 1) w) r (tail deltas) :=
  fun i => by simp only [get_tail, Stream'.drop_drop]; exact h (i + 1)

theorem charOmegaHead {w : Stream' σ} {r : ERE α} {deltas : Stream' ℕ}
  (h : IsDeltasOmegaLanguage w r deltas) :
  take ((head deltas) + 1) w ⊫ r := h 0

theorem take_length_append : Stream'.take (length s) (s ++ₛ w) = s := by
  match s with
  | [] => simp only [length_nil, Stream'.take_zero]
  | .cons a s =>
    erw[Stream'.take_succ,Stream'.cons_append_stream]
    simp only [get_zero_cons, Stream'.tail_cons, cons.injEq, true_and]
    exact take_length_append

theorem charOmegaCons {w : Stream' σ} {r : ERE α} {deltas : Stream' ℕ}
  (h : IsDeltasOmegaLanguage w r deltas) (m : a :: str ⊫ r):
  -- we just put str and not a :: str because in the stream the length is minus one
  IsDeltasOmegaLanguage ((a :: str) ++ₛ w) r (length str :: deltas) :=
  fun i =>
  match i with
  | 0 => by
    simp only [get_zero_cons, getWordStart, Stream'.drop_zero]
    rw[←Nat.succ_eq_add_one,←length_cons a str,take_length_append]
    exact m
  | Nat.succ i => by
    simp only [get_succ_cons, getWordStart, Stream'.tail_cons, get_zero_cons]
    rw[←Stream'.drop_drop,←Nat.succ_eq_add_one]
    rw[←Nat.succ_eq_add_one,←length_cons a str,Stream'.drop_append_stream]
    exact (h i)

theorem regexOmegaClosure {r : ERE α} :
  w ∈* r ↔ (∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r) :=
  ⟨fun ⟨deltas, h⟩ =>
   ⟨head deltas + 1,
    by simp only [gt_iff_lt, add_pos_iff, zero_lt_one, or_true],
    charOmegaHead h,⟨Stream'.tail deltas,charOmegaDrop h⟩⟩,
   fun ⟨i,hi,h1,⟨deltas,h⟩⟩ =>
   match i with
   | 0 => by simp only [gt_iff_lt, lt_self_iff_false] at hi
   | Nat.succ i => by
     exists i::deltas
     intro j
     match j with
     | 0 => simp only [get_zero_cons, getWordStart, Stream'.drop_zero]; exact h1
     | Nat.succ j =>
       simp only [get_succ_cons, getWordStart, Stream'.tail_cons, get_zero_cons]
       have := h j
       simp only [Stream'.drop_drop] at this
       rw[←Nat.succ_eq_add_one] at this; exact this⟩
