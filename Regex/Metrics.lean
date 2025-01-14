import Regex.Definitions

/-!
# Metrics

Collection of all the various metrics used in the formalization
to ensure the well-foundedness of the algorithm.
-/

open ERE RLTL

/-- Size of metric function, counting the number of constructors. -/
@[simp]
def sizeOf_ERE (r : ERE α) : ℕ :=
  match r with
  | ε          => 0
  | ERE.Pred _ => 0
  | l ⋓ r      => 1 + sizeOf_ERE l + sizeOf_ERE r
  | l ⋒ r      => 1 + sizeOf_ERE l + sizeOf_ERE r
  | l ⬝ r      => 1 + sizeOf_ERE l + sizeOf_ERE r
  | r *        => 1 + sizeOf_ERE r
  | ~ r        => 1 + sizeOf_ERE r
  | l : r      => 1 + sizeOf_ERE l + sizeOf_ERE r

instance : WellFoundedRelation (ℕ ×ₗ ℕ) where
  rel := (· < ·)
  wf  := WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf

/-- Lexicographic combination of star height and size of regexp. -/
def star_metric (r : ERE α) : ℕ ×ₗ ℕ :=
  match r with
  | ε          => (0, 0)
  | ERE.Pred _ => (0, 0)
  | l ⋓ r      => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⋒ r      => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⬝ r      => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | r *        => (1 + (star_metric r).1, 1 + (star_metric r).2)
  | ~ r        => ((star_metric r).1, 1 + (star_metric r).2)
  | l : r      => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)

theorem star_metric_catL :
  star_metric l < (star_metric (l ⬝ r)) := by
  simp [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMaxNat maxOfLe; simp
  split
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)

theorem star_metric_catR :
  star_metric r < (star_metric (l ⬝ r)) := by
  simp only [star_metric, ge_iff_le];
  unfold LT.lt Prod.Lex.instLT max Nat.instMaxNat maxOfLe; simp
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem star_metric_altL :
  star_metric l < (star_metric (l ⋓ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMaxNat maxOfLe; simp
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp_rw [g]; simp only [ite_true]
    by_cases g1 : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←g1]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g g1)
  . simp_rw [g]; simp [ite_false]
    exact Prod.Lex.right _ (by linarith)

theorem star_metric_altR :
  star_metric r < (star_metric (l ⋓ r)) := by
  simp only [star_metric, ge_iff_le];
  unfold LT.lt Prod.Lex.instLT max Nat.instMaxNat maxOfLe; simp
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem star_metric_repeat_first :
  (star_metric (r ⁽ n ⁾)).fst < 1 + (star_metric r).fst :=
  match n with
  | 0          => by simp[star_metric]
  | Nat.succ n => by
    simp [star_metric, ge_iff_le, max_lt_iff, lt_add_iff_pos_left, true_and]
    apply (@star_metric_repeat_first _ r n)

theorem star_metric_star :
  star_metric (repeat_cat r m) < star_metric (r *) := by
   simp only [star_metric]; apply Prod.Lex.left
   apply star_metric_repeat_first

theorem star_metric_neg :
  star_metric r < (star_metric (~ r)) := by
  simp only [star_metric]
  apply Prod.Lex.right _ (by simp [lt_add_iff_pos_left])

theorem star_metric_interL :
  star_metric l < (star_metric (l ⋒ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMaxNat maxOfLe; simp only
  split
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . simp only at h
      exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)

theorem star_metric_interR :
  star_metric r < (star_metric (l ⋒ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMaxNat maxOfLe; simp only
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

/-- The termination metric is needed to show the well-foundedness of the derivativeRLTL function. -/
@[simp]
def sizeOf_RLTL : RLTL α → ℕ
  | RLTL.Pred _    => 0
  | ¬ₗ φ           => 1 + sizeOf_RLTL φ
  | φ ∧ₗ ψ         => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | φ ∨ₗ ψ         => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | φ →ₗ ψ         => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | X φ            => 1 + sizeOf_RLTL φ
  | φ U ψ          => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | φ R ψ          => 1 + sizeOf_RLTL φ + sizeOf_RLTL ψ
  | r ◇→ φ         => 1 + sizeOf_ERE r + sizeOf_RLTL φ
  | r ▫→ φ         => 1 + sizeOf_ERE r + sizeOf_RLTL φ
  | ⦃ r ⦄          => 1 + sizeOf_ERE r
  | OmegaClosure r => 1 + sizeOf_ERE r
