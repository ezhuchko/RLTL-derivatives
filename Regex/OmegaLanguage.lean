import Regex.EREMatchSemantics
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool

/-!
# Omega language

Contains the specification of omega languages.

-/


variable {α σ : Type} [EffectiveBooleanAlgebra α σ] [DecidableEq α] [DecidableEq σ]

open List Stream' TTerm ERE RLTL

@[simp]
def getWordStart (w : Stream' ℕ) (i : ℕ) : ℕ :=
  match i with
  | 0 => 0
  | .succ i => getWordStart (tail w) i + (head w + 1)

@[simp]
def IsDeltasOmegaLanguage (w : Stream' σ) (r : ERE α) (deltas : Stream' ℕ) : Prop :=
  ∀ (i : ℕ),                            -- for all starting indices (of all subwords)
    let start := getWordStart deltas i  -- get the starting index of the subword
    let len := get deltas i + 1         -- get the length of the subword
    take len (drop start w) ⊫ r         -- check that it is in the language of r

def InOmegaLanguage (w : Stream' σ) (r : ERE α) : Prop :=
  ∃ (deltas : Stream' ℕ), IsDeltasOmegaLanguage w r deltas

infixr:40 " ∈* "  => InOmegaLanguage

theorem charOmegaDrop {w : Stream' σ} {r : ERE α} {deltas : Stream' ℕ}
  (h : IsDeltasOmegaLanguage w r deltas) :
  IsDeltasOmegaLanguage (drop (head deltas + 1) w) r (tail deltas) :=
  fun i => by simp; exact h (i + 1)

theorem charOmegaHead {w : Stream' σ} {r : ERE α} {deltas : Stream' ℕ}
  (h : IsDeltasOmegaLanguage w r deltas) :
  take ((head deltas) + 1) w ⊫ r := h 0

theorem take_length_append : Stream'.take (length s) (s ++ₛ w) = s := by
  match s with
  | [] => simp
  | .cons a s =>
    erw[Stream'.take_succ,Stream'.cons_append_stream]
    simp; exact take_length_append

theorem charOmegaCons {w : Stream' σ} {r : ERE α} {deltas : Stream' ℕ}
  (h : IsDeltasOmegaLanguage w r deltas) (m : a :: str ⊫ r):
  -- we just put str and not a :: str because in the stream the length is minus one
  IsDeltasOmegaLanguage ((a :: str) ++ₛ w) r (length str :: deltas) := by
  intro i
  match i with
  | 0 =>
    simp; rw[←Nat.succ_eq_add_one,←length_cons a str,take_length_append]
    exact m
  | Nat.succ i =>
    simp; rw[←Stream'.drop_drop,←Nat.succ_eq_add_one]
    rw[←Nat.succ_eq_add_one,←length_cons a str,Stream'.drop_append_stream]
    exact (h i)

theorem regexOmegaClosure {r : ERE α} : w ∈* r → (∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r) :=
  fun ⟨deltas, h⟩ =>
  ⟨head deltas + 1,by simp,charOmegaHead h,⟨Stream'.tail deltas,charOmegaDrop h⟩⟩
