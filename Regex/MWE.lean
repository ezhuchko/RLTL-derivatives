import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool
import Batteries.Data.Nat.Lemmas

variable {α σ : Type}

open List Stream'

axiom Pl : List α → Prop
axiom Pr : List α → Prop
axiom incremental : Pl xs → Pr ys → Pl (xs ++ ys)

def StreamIsSectionedUsingProp (w : Stream' Nat) : Prop :=
   ∀ (i : ℕ), Pl (Stream'.take (i + 1) w)
      → ∃! j, Pr (Stream'.take (j + 1) (Stream'.drop (i + 1) w))

abbrev Index : Type := ℕ

abbrev Delta : Type := Index → ℕ

@[simp]
def getWordStart (deltas : Delta) (i : Index) : ℕ :=
  match i with
  | 0 => 0
  | .succ i => (head deltas + 1) + getWordStart (tail deltas) i

@[simp]
def IsSectionedDelta (w : Stream' σ) (deltas : Delta) : Prop :=
  ∀ (i : Index),
    let start := getWordStart deltas i
    let len := get deltas i + 1
    Pr (take len (drop start w))

def StreamIsSectionedUsingDelta (w : Stream' σ) : Prop :=
  ∃ (deltas : Delta), IsSectionedDelta w deltas

theorem equiv1 (p : StreamIsSectionedUsingProp w) :
    StreamIsSectionedUsingDelta w := by
  sorry
