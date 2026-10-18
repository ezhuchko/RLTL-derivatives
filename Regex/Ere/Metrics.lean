import Mathlib.Order.Prod.Lex.Basic
import Regex.Ere.Definitions

open Ere

/-
# Metrics

Collection of all the various metrics used in the formalisation
to ensure termination.
-/

/-- Star height, counting the level of nested applications of star. -/
@[simp]
def starHeight (R : Ere α) : Nat :=
  match R with
  | ε | Pred _ => 0
  | l ⋓ r | l ⋒ r | l ⬝ r | l : r => max (starHeight l) (starHeight r)
  | .Star r => 1 + starHeight r
  | ~ r => starHeight r

/-- Lexicographic combination of star height and size of regex. -/
@[simp]
noncomputable def starMetric (R : Ere α) : Nat ×ₗ Nat := (starHeight R, sizeOf R)

/-! ### The star metric decreases on subexpressions -/

theorem lex_lt_max_left {a b x y : Nat} : toLex (a, x) < toLex (max a b, 1 + x + y) :=
  Prod.Lex.toLex_lt_toLex.mpr (by omega)

theorem lex_lt_max_right {a b x y : Nat} : toLex (b, y) < toLex (max a b, 1 + x + y) :=
  Prod.Lex.toLex_lt_toLex.mpr (by omega)

theorem lex_lt_succ {a x : Nat} : toLex (a, x) < toLex (a, 1 + x) :=
  Prod.Lex.toLex_lt_toLex.mpr (by omega)

theorem starMetric_Cat_l : starMetric l < starMetric (l ⬝ r) := lex_lt_max_left
theorem starMetric_Cat_r : starMetric r < starMetric (l ⬝ r) := lex_lt_max_right
theorem starMetric_Alt_l : starMetric l < starMetric (l ⋓ r) := lex_lt_max_left
theorem starMetric_Alt_r : starMetric r < starMetric (l ⋓ r) := lex_lt_max_right
theorem starMetric_Inter_l : starMetric l < starMetric (l ⋒ r) := lex_lt_max_left
theorem starMetric_Inter_r : starMetric r < starMetric (l ⋒ r) := lex_lt_max_right
theorem starMetric_Fusion_l : starMetric l < starMetric (l : r) := lex_lt_max_left
theorem starMetric_Fusion_r : starMetric r < starMetric (l : r) := lex_lt_max_right

@[simp]
theorem starMetric_Negation : starMetric r < starMetric (~ r) := lex_lt_succ

theorem starMetric_Star : starMetric r < starMetric (r *) :=
  Prod.Lex.left _ _ (by simp)

theorem starMetric_repeat_first : starHeight (r ⁽ n ⁾) < 1 + starHeight r := by
  induction n with
  | zero => simp; omega
  | succ n ih => simp_all

theorem starMetric_repeat : starMetric (r ⁽ n ⁾) < starMetric (r *) :=
  Prod.Lex.left _ _ starMetric_repeat_first
