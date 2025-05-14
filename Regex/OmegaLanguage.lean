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

/-- This predicate checks whether a stream `w` is in the ω-closure of `r` i.e. `w ∈ r*?`.-/
@[simp]
def IsBound (w : Stream' σ) (r : ERE α) (isBound : ℕ → Bool) : Prop :=
    isBound 0
  ∧ ∀ i, isBound i
    → ∃ len > 0, Stream'.take len (Stream'.drop i w) ⊫ r
                ∧ isBound (i + len)

@[simp]
def InOmegaLanguage (w : Stream' σ) (r : ERE α) : Prop :=
  ∃ (isBound : ℕ → Bool), IsBound w r isBound

theorem base_case' {r : ERE α} {isBound : ℕ → Bool} (h : IsBound w r isBound) :
  ∃ l > 0, Stream'.take l w ⊫ r ∧ isBound l :=
  let ⟨d0, h1⟩ := h;
  let ⟨p1 + 1,p2,pl,mi⟩ := h1 0 d0;
  by simp at mi
     exact ⟨p1 + 1, p2, pl, mi⟩

infixr:40 " ∈* "  => InOmegaLanguage

theorem take_length_append : Stream'.take (length s) (s ++ₛ w) = s := by
  match s with
  | [] => simp only [length_nil, Stream'.take_zero]
  | .cons a s =>
    erw[Stream'.take_succ,Stream'.cons_append_stream]
    simp only [get_zero_cons, Stream'.tail_cons, cons.injEq, true_and]
    exact take_length_append

theorem lemma11 (h : j ≥ ws.length) w
   : Stream'.drop (j - ws.length) w = Stream'.drop j (ws ++ₛ w) := by
  match ws with
  | [] =>
    simp only [length_nil, Stream'.drop_zero]
    simp
  | .cons _ ws =>
    match j with
    | 0 => contradiction
    | j + 1 =>
      simp at h
      have := lemma11 h w
      simp
      rw[this]
      rw[Stream'.drop_succ]
      rw[Stream'.cons_append_stream]
      simp

theorem concat_stream {r : ERE α} (wn0 : ws.length > 0)
  (left : ws ⊫ r) (h : w ∈* r) :
  ws ++ₛ w ∈* r := by
  let ⟨deltas,d0,h1⟩ := h
  exists
    (fun j =>
        if j >= ws.length then
          deltas (j - ws.length)
        else
          j = 0)
  apply And.intro
  . simp
    aesop
  . intro j
    intro l
    by_cases eq:j >= ws.length
    . simp at l
      simp_rw[eq] at l
      dsimp at l
      dsimp
      have ⟨len,lgz,m1,m2⟩ := h1 (j - ws.length) l
      exists len
      exists lgz
      rw[lemma11 eq w] at m1
      exists m1
      have : j + len ≥ ws.length := by linarith
      simp_rw[this]
      simp
      rw[←Nat.sub_add_comm eq] at m2
      exact m2
    . simp_rw[eq] at l
      simp at l
      subst l
      dsimp
      exists ws.length
      exists wn0
      exists (by
        simp[take_length_append]
        exact left)
      simp
      have := h1
      exact d0

theorem regexOmegaClosureOneD {r : ERE α} (h : w ∈* r)
  : ∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r := by
  let ⟨isBound, b0, h0⟩ := h
  have ⟨ws,a2,a3,a4⟩ := h0 0 b0
  exists ws
  exists a2
  exists a3
  exists λ j => isBound (ws + j)
  dsimp
  simp at a4
  exists a4
  intro i m
  have ⟨bs,b2,b3,b4⟩ := h0 _ m
  exists bs
  exists b2
  simp[Stream'.drop_drop]
  exists b3
  rw[←Nat.add_assoc]
  exact b4

theorem regexOmegaClosure {r : ERE α} :
  w ∈* r ↔ (∃ i > 0, take i w ⊫ r ∧ drop i w ∈* r) :=
  ⟨regexOmegaClosureOneD,
   λ ⟨i, o, p, q⟩ =>
     have := concat_stream (by simp; exact o) p q
     by rw[Stream'.append_take_drop] at this
        exact this⟩

theorem semmm {r : ERE α} (a : xs ⊫ r) (b : ys ⊫ r*) :
  xs ++ ys ⊫ r* := by
  simp at b
  let ⟨m,hm⟩ := b
  simp
  exists m + 1
  simp
  exists xs; exists a; exists ys

theorem semmm' {r : ERE α} (a : xs ⊫ r*) (b : ys ⊫ r) :
  xs ++ ys ⊫ r* := by
  simp
  simp at a
  let ⟨m,hm⟩ := a
  have := equiv_repeat_cat_cat (r:=r) (m:=m) (xs:=xs++ys)
  exists m + 1
  simp only [repeat_cat]
  rw[←this]
  simp
  exists xs; exists hm; exists ys
