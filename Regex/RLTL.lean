import Regex.ERE
import Regex.OmegaLanguage
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool

/-!
# RLTL derivation

Contains match semantics and derivation rules for RLTL, as well as the main
derivation theorem.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List Stream' TTerm ERE RLTL EffectiveBooleanAlgebra

/-- OneStep of r is a predicate which looks one derivative step ahead. -/
def OneStep (r : ERE α) : α := OneStep' (derivative r)

/-- The derivatives of RLTL are defined using transition terms, `TTerm⟨α,RLTL α⟩`, where
    `α` is the type of alphabet and `RLTL α` is the type of leaves. -/
@[simp]
def RLTL.derivative (r : RLTL α) : TTerm α (RLTL α) :=
  match r with
  | .Pred a => Node a (.pure (Pred ⊤)) (.pure (Pred ⊥))
  | ¬ₗ φ    => lift_unary (¬ₗ ·) (derivative φ)
  | φ ∧ₗ ψ  => lift_binary (· ∧ₗ ·) (derivative φ) (derivative ψ)
  | φ ∨ₗ ψ  => lift_binary (· ∨ₗ ·) (derivative φ) (derivative ψ)
  | X φ     => TTerm.pure φ
  | φ U ψ   =>
    let rhs := lift_binary (· ∧ₗ ·) (derivative φ) (.pure (φ U ψ))
    lift_binary (· ∨ₗ ·) (derivative ψ) rhs
  | φ R ψ   =>
    let rhs := lift_binary (· ∨ₗ ·) (derivative φ) (.pure (φ R ψ))
    lift_binary (· ∧ₗ ·) (derivative ψ) rhs
  | φ →ₗ ψ  => lift_binary (· →ₗ ·) (derivative φ) (derivative ψ)
  | r ﹕﹕ φ  =>
    let lhs := Node (OneStep r) (derivative φ) (.pure (Pred ⊥))
    lift_binary (· ∨ₗ ·) lhs (lift_unary (· ﹕﹕ φ) (δ r))
  | r :> φ  =>
    let lhs := Node (OneStep r) (derivative φ) (.pure (Pred ⊤))
    lift_binary (· ∧ₗ ·) lhs (lift_unary (· :> φ) (δ r))
  | ⦃ r ⦄   =>
    if nullable r then
      .pure (Pred ⊤)
    else
      lift_unary (⦃ . ⦄) (δ r)
  | r^ω     =>
    let lhs := lift_binary (· ∧ₗ ·) (derivative (Pred (OneStep r)))
                                    (.pure r^ω)
    lift_binary (· ∨ₗ ·) lhs (lift_unary (· ﹕﹕ X (r^ω)) (δ r))
termination_by sizeOf_RLTL r
prefix:max " 𝜕 " => RLTL.derivative

/-- Multi-step evaluation function. -/
def RLTL.multi_step : RLTL α → List σ → Stream' σ → RLTL α
  | φ, [], _ => φ
  | φ, .cons a as, w => multi_step ((𝜕 φ) [a]) as w

/-- The semantics of RLTL are formalised using the models relation. -/
@[simp]
def RLTL.models (w : Stream' σ) : RLTL α → Prop
  | .Pred p => head w ⊨ p
  | ¬ₗ φ    => ¬ models w φ
  | φ ∧ₗ ψ  => models w φ ∧ models w ψ
  | φ ∨ₗ ψ  => models w φ ∨ models w ψ
  | X φ     => models (tail w) φ
  | φ U ψ   =>
    ∃ j, models (drop j w) ψ ∧ ∀ i < j, models (drop i w) φ
  | φ R ψ   =>
      (∀ i, models (drop i w) ψ)
    ∨ (∃ j, models (drop j w) φ ∧ ∀ k ≤ j, models (drop k w) ψ)
  | φ →ₗ ψ  => models w φ → models w ψ
  | r ﹕﹕ φ  =>
    ∃ i, take (i + 1) w ⊫ r ∧ models (drop i w) φ
  | r :> φ  =>
    ∀ i, take (i + 1) w ⊫ r → models (drop i w) φ
  | ⦃ r ⦄   =>
    (∃ i,   take i w ⊫ r) ∨ (∀ i > 0, ∃ x, take i w ++ x ⊫ r)
  | r^ω     => w ∈* r
notation:52 lhs:53 " |= " rhs:53 => RLTL.models lhs rhs

@[simp]
theorem expansion_until {φ ψ : RLTL α} :
  w |= (φ U ψ) ↔ w |= (ψ ∨ₗ (φ ∧ₗ X(φ U ψ))) := by
  simp only [RLTL.models, drop_tail']
  apply Iff.intro
  . intro ⟨j,h1,h2⟩
    match j with
    | 0 => simp only [Stream'.drop_zero] at h1; exact Or.inl h1
    | .succ j =>
      apply Or.inr ⟨h2 0 (Nat.zero_lt_succ j),j,h1,
                    λ i hi => h2 i.succ (by linarith)⟩
  . intro h
    match h with
    | Or.inl h1 =>
      exact ⟨0,h1,λ i hi => by simp only [not_lt_zero'] at hi⟩
    | Or.inr ⟨h1,j,h2,h3⟩ =>
      exact ⟨j.succ,h2,
             λ i _ =>
             match i with
             | 0 => h1
             | .succ i => h3 i (by linarith)⟩

@[simp]
theorem expansion_release {φ ψ : RLTL α} :
  w |= (φ R ψ) ↔ w |= (ψ ∧ₗ (φ ∨ₗ X(φ R ψ))) := by
  simp only [RLTL.models, drop_tail']
  apply Iff.intro
  . intro h
    match h with
    | Or.inl h1 =>
      exact ⟨h1 0,Or.inr $ Or.inl (λ i => h1 i.succ)⟩
    | Or.inr ⟨j,h1,h2⟩ =>
      match j with
      | 0 =>
        simp only [Stream'.drop_zero, nonpos_iff_eq_zero, forall_eq] at h1 h2
        exact ⟨h2,Or.inl h1⟩
      | .succ j =>
        exact ⟨h2 0 (Nat.zero_le (Nat.succ j)),
               Or.inr $ Or.inr ⟨j,h1,λ i hi => h2 i.succ (by linarith)⟩⟩
  . intro ⟨h1,h2⟩
    match h2 with
    | Or.inl h3 =>
      apply Or.inr ⟨0,by simp only [Stream'.drop_zero]; exact h3,
                    λ i hi => by simp only [nonpos_iff_eq_zero] at hi
                                 subst hi; simp only [Stream'.drop_zero]; exact h1⟩
    | Or.inr h3 =>
      match h3 with
      | Or.inl h4 =>
        apply Or.inl
        intro j
        match j with
        | 0 => simp only [Stream'.drop_zero]; exact h1
        | .succ j => exact h4 j
      | Or.inr ⟨j,h4,h5⟩ =>
        match j with
        | 0 =>
          apply Or.inr ⟨1,h4,λ k h =>
                             match k with
                             | 0 => h1
                             | .succ k => by simp only [Nat.succ_le_iff, Nat.lt_one_iff] at h
                                             subst h; exact h5 0 (Subarray.empty.proof_1)⟩
        | .succ i =>
          apply Or.inr ⟨i.succ.succ,h4,
                        λ k _ =>
                        match k with
                        | 0 => h1
                        | .succ k => h5 k (by linarith)⟩

/-- An example of an algebraic rewrite rule: the existential suffix implication operator distributes
    over union. -/
theorem esi_distributivity {l r : ERE α} {φ : RLTL α} :
  w |= ((l ⋓ r) ﹕﹕ φ) ↔ w |= (l ﹕﹕ φ) ∨ w |= (r ﹕﹕ φ) := by
  simp only [RLTL.models, ERE.models]
  apply Iff.intro
  . intro ⟨i,h1,h2⟩
    match h1 with
    | Or.inl h1 => exact Or.inl ⟨i,h1,h2⟩
    | Or.inr h1 => exact Or.inr ⟨i,h1,h2⟩
  . intro h
    match h with
    | Or.inl ⟨i,h1,h2⟩ => exact ⟨i,Or.inl h1,h2⟩
    | Or.inr ⟨i,h1,h2⟩ => exact ⟨i,Or.inr h1,h2⟩

/-- An example of an algebraic rewrite rule: the universala suffix implication operator distributes
    over union. -/
theorem usi_distributivity {l r : ERE α} {φ : RLTL α} :
  w |= ((l ⋓ r) :> φ) ↔ w |= (l :> φ) ∧ w |= (r :> φ) := by
  simp only [RLTL.models, ERE.models]
  apply Iff.intro
  . intro h; exact ⟨λ i hi => h i (Or.inl hi), λ i hi => h i (Or.inr hi)⟩
  . intro h i hi
    match hi with
    | Or.inl hi => exact h.1 i hi
    | Or.inr hi => exact h.2 i hi

/-- The main theorem (Theorem 4 in the paper) proving correctness of the derivation rules for RLTL. -/
theorem RLTL.derivation {φ : RLTL α} :
  a::w |= φ ↔ w |= (𝜕 φ) [a] :=
  match φ with
  | RLTL.Pred p => by
    simp only [RLTL.models, modelsEBA, get_zero_cons, evaluation]
    by_cases h : denote p a
    . simp only [h, ↓reduceIte, RLTL.models, modelsEBA, denote_top]
    . simp only [h, ↓reduceIte, RLTL.models, modelsEBA, denote_bot]
  | ¬ₗ φ => by
    simp only [RLTL.models, RLTL.derivative, liftU]
    apply not_congr RLTL.derivation -- inductive hypothesis
  | φ ∧ₗ ψ => by
    simp only [RLTL.models, RLTL.derivative, liftB]
    apply and_congr RLTL.derivation RLTL.derivation -- inductive hypothesis
  | φ ∨ₗ ψ => by
    simp only [RLTL.models, RLTL.derivative, liftB]
    apply or_congr RLTL.derivation RLTL.derivation -- inductive hypothesis
  | φ →ₗ ψ => by
    simp only [RLTL.models, RLTL.derivative, liftB]
    apply imp_congr RLTL.derivation RLTL.derivation -- inductive hypothesis
  | X φ => by
    simp only [RLTL.models, Stream'.tail_cons, RLTL.derivative, TTerm.pure, evaluation]
  | φ U ψ => by
    rw [expansion_until]
    simp only [RLTL.models, Stream'.tail_cons,
               RLTL.derivative, TTerm.pure, liftB, evaluation]
    rw [RLTL.derivation,RLTL.derivation] -- inductive hypothesis
  | φ R ψ => by
    rw [expansion_release]
    simp only [RLTL.models, Stream'.tail_cons, RLTL.derivative, TTerm.pure,
               liftB, evaluation]
    rw [RLTL.derivation,RLTL.derivation] -- inductive hypothesis
  | r ﹕﹕ ψ => by
    simp only [RLTL.models, RLTL.derivative, liftB, liftU]
    by_cases g : denote (OneStep r) a
    . simp only [Stream'.take_succ_cons, evaluation, g, ↓reduceIte]
      apply Iff.intro
      . intro ⟨i,h1,h2⟩
        match i with
        | 0       => exact Or.inl (RLTL.derivation.mp h2) -- inductive hypothesis
        | .succ i => exact Or.inr ⟨i,ERE.derivation.mp h1,h2⟩
      . intro h
        match h with
        | Or.inl h1        =>
          exact ⟨0,ERE.derivation.mpr (denoteOneStep.mpr g),RLTL.derivation.mpr h1⟩ -- inductive hypothesis
        | Or.inr ⟨i,h1,h2⟩ => exact ⟨i.succ,ERE.derivation.mpr h1,h2⟩
    . simp only [Stream'.take_succ_cons, evaluation, g, ↓reduceIte, RLTL.models,
                 modelsEBA, denote_bot, false_or]
      apply Iff.intro
      . intro ⟨i,h1,h2⟩
        match i with
        | 0       =>
          simp only [Stream'.take_zero] at h1
          erw [←denoteOneStep] at g
          have := ERE.derivation (r:=r) (xs:=[]) (a:=a)
          rw [this] at h1
          contradiction
        | .succ i => exact ⟨i,ERE.derivation.mp h1,h2⟩
      . intro ⟨i,h1,h2⟩; exact ⟨i.succ,ERE.derivation.mpr h1,h2⟩
  | r :> φ => by
    simp only [RLTL.models, RLTL.derivative, liftB, liftU]
    by_cases g : denote (OneStep r) a
    . simp only [Stream'.take_succ_cons, evaluation, g, ↓reduceIte]
      apply Iff.intro
      . intro h
        have h1 := h 0 (ERE.derivation.mpr (denoteOneStep.mpr g))
        exact ⟨RLTL.derivation.mp h1,
               λ i hi => h i.succ (ERE.derivation.mpr hi)⟩ -- inductive hypothesis
      . intro ⟨h1,h2⟩ i hi
        match i with
        | 0       => exact (RLTL.derivation.mpr h1) -- inductive hypothesis
        | .succ i => exact h2 i (ERE.derivation.mp hi)
    . simp only [Stream'.take_succ_cons, evaluation, g, ↓reduceIte, RLTL.models,
                 modelsEBA, denote_top, true_and]
      apply Iff.intro
      . intro h i hi; exact (h i.succ (ERE.derivation.mpr hi))
      . intro h i hi
        match i with
        | 0       =>
          simp only [Stream'.take_zero] at hi
          erw [←denoteOneStep, ←ERE.derivation] at g
          contradiction
        | .succ i => exact h i (ERE.derivation.mp hi)
  | ⦃ r ⦄ => by
    simp only [RLTL.models, gt_iff_lt, RLTL.derivative, TTerm.pure]
    by_cases g : nullable r
    . simp only [g, ↓reduceIte, RLTL.models, modelsEBA, denote_top, iff_true]
      exact Or.inl ⟨0,(equivalenceNull (r:=r)).mpr g⟩
    . simp only [g, ↓reduceIte, liftU, RLTL.models, gt_iff_lt]
      apply Iff.intro
      . intro h
        match h with
        | Or.inl ⟨i,h1⟩ =>
          match i with
          | 0       =>
            simp only [Stream'.take_zero, equivalenceNull] at h1
            contradiction
          | .succ i => exact Or.inl ⟨i,ERE.derivation.mp h1⟩
        | Or.inr h1 =>
          apply Or.inr
          intro i hi
          match i with
          | 0       => simp only [lt_self_iff_false] at hi -- contradiction
          | .succ i =>
            have ⟨k1,k2⟩ := h1 i.succ.succ (by linarith)
            exact ⟨k1,ERE.derivation.mp k2⟩
      . intro h
        match h with
        | Or.inl ⟨i,h1⟩ => exact Or.inl ⟨i.succ,ERE.derivation.mpr h1⟩
        | Or.inr h1 =>
          apply Or.inr; intro i hi
          match i with
          | 0       => simp only [lt_self_iff_false] at hi -- contradiction
          | .succ i =>
            match i with
            | 0 =>
              have ⟨j1,j2⟩ := h1 1 (by linarith)
              exact ⟨(Stream'.take 1 w ++ j1),ERE.derivation.mpr j2⟩
             | .succ i =>
               have ⟨j1,j2⟩ := h1 i.succ (by linarith)
               exact ⟨j1,ERE.derivation.mpr j2⟩
  | r^ω => by
    simp only [RLTL.models, RLTL.derivative, TTerm.pure, liftB, evaluation,
               liftU, tail_drop']
    by_cases g : denote (OneStep r) a
    . simp only [g, ↓reduceIte, RLTL.models, modelsEBA, denote_top, true_and]
      apply Iff.intro
      . intro ⟨deltas,proof⟩
        have h1 := charOmegaDrop proof
        by_cases p : head deltas = 0
        . rw [p,tail_eq_drop] at h1; exact Or.inl ⟨tail deltas,h1⟩
        . match hp : get deltas 0 with
          | 0 => contradiction
          | .succ n =>
            have gg2 := proof 0
            simp only [hp, getWordStart, Stream'.drop_zero, Stream'.take_succ_cons] at gg2
            erw [←Stream'.head_drop,Stream'.drop_zero] at hp
            rw [hp,drop_succ] at h1
            exact Or.inr ⟨n,ERE.derivation.mp gg2,tail deltas,h1⟩
      . intro h
        match h with
        | Or.inl ⟨deltas,h2⟩ => exact ⟨0::deltas,charOmegaCons h2 (ERE.derivation.mpr (denoteOneStep.mpr g))⟩
        | Or.inr ⟨i,h1,⟨deltas,proof⟩⟩ =>
          have gg := charOmegaCons proof (ERE.derivation.mpr h1)
          simp only [IsDeltasOmegaLanguage, Stream'.length_take, cons_append_stream,
            append_take_drop] at gg
          exact ⟨i.succ::deltas,gg⟩
    . simp only [g, ↓reduceIte, RLTL.models, modelsEBA, denote_bot, false_and, false_or]
      apply Iff.intro
      . intro ⟨deltas,h1⟩
        have h2 := charOmegaHead h1
        match hp : head deltas with
        | 0 =>
          simp only [hp, zero_add, Stream'.take_succ_cons, Stream'.take_zero] at h2
          erw [←denoteOneStep, ←ERE.derivation] at g
          contradiction
        | .succ n =>
          simp only [hp, Stream'.take_succ_cons, ERE.derivation] at h2
          have t := charOmegaDrop h1
          rw [hp,drop_succ] at t
          exact ⟨n,h2,tail deltas,t⟩
      . intro ⟨i,pr,deltas,proof⟩
        erw [←append_take_drop (i+1) w,←cons_append_stream]
        exact ⟨length (take (i + 1) w)::deltas,charOmegaCons proof (ERE.derivation.mpr pr)⟩

theorem RLTL.derivationMultiStep {φ : RLTL α} {u : List σ} {w : Stream' σ} :
  Stream'.appendStream' u w |= φ ↔ w |= multi_step φ u w :=
  match u with
  | [] => by simp only [RLTL.multi_step, Stream'.nil_append_stream]
  | .cons a as => by
    simp only [RLTL.multi_step]
    erw[derivation]
    rw[RLTL.derivationMultiStep]
