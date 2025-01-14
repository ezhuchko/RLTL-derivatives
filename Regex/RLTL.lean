import Regex.EREMatchSemantics
import Regex.OmegaLanguage
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool

/-!
# RLTL derivation

Contains match semantics and derivation rules for RLTL, as well as the main
derivation theorem.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ] [DecidableEq α] [DecidableEq σ]

open List Stream' TTerm ERE RLTL

/-- OneStep of r is a predicate which looks one derivative step ahead. -/
def OneStep (r : ERE α) := OneStep' (derivative r)

/-- The derivatives of RLTL are defined using transition terms (TTerm). -/
def RLTL.derivative (r : RLTL α) : TTerm α (RLTL α) :=
  match r with
  | RLTL.Pred a  => Node a (TTerm.pure (Pred ⊤)) (TTerm.pure (Pred ⊥))
  | ¬ₗ φ   => lift_unary (¬ₗ ·) (derivative φ)
  | φ ∧ₗ ψ => lift_binary (· ∧ₗ ·) (derivative φ) (derivative ψ)
  | φ ∨ₗ ψ => lift_binary (· ∨ₗ ·) (derivative φ) (derivative ψ)
  | X φ    => TTerm.pure φ
  | φ U ψ  =>
    let a := lift_binary (· ∧ₗ ·) (derivative φ) (TTerm.pure (φ U ψ))
    lift_binary (· ∨ₗ ·) (derivative ψ) a
  | φ R ψ  =>
    let a := lift_binary (· ∨ₗ ·) (derivative φ) (TTerm.pure (φ R ψ))
    lift_binary (· ∧ₗ ·) (derivative ψ) a
  | φ →ₗ ψ => lift_binary (· →ₗ ·) (derivative φ) (derivative ψ)
  | r ◇→ φ =>
    let lhs := Node (OneStep r) (derivative φ) (Leaf (Pred ⊥))
    lift_binary (· ∨ₗ ·) lhs (lift_unary (fun x => x ◇→ φ) (δ r))
  | r ▫→ φ =>
    let lhs := Node (OneStep r) (derivative φ) (Leaf (Pred ⊤))
    lift_binary (· ∧ₗ ·) lhs (lift_unary (fun x => x ▫→ φ) (δ r))
  | ⦃ r ⦄ =>
    if nullable r then
      TTerm.pure (Pred ⊤)
    else
      lift_unary (⦃ . ⦄) (δ r)
  | r^ω   =>
    let lhs := lift_binary (· ∧ₗ ·) (derivative (Pred (OneStep r)))
                                    (TTerm.pure r^ω)
    lift_binary (· ∨ₗ ·) lhs (lift_unary (fun x => x ◇→ X (r^ω)) (δ r))
termination_by sizeOf_RLTL r
prefix:max " 𝜕 " => RLTL.derivative

/-- The semantics of RLTL are formalised using the models relation. -/
def RLTL.models (w : Stream' σ) : RLTL α → Prop
  | RLTL.Pred p => head w ⊨ p
  | ¬ₗ φ        => ¬ models w φ
  | φ ∧ₗ ψ      => models w φ ∧ models w ψ
  | φ ∨ₗ ψ      => models w φ ∨ models w ψ
  | X φ         => models (tail w) φ
  | φ U ψ       =>
    ∃ j,   models (drop j w) ψ ∧ ∀ i < j, models (drop i w) φ
  | φ R ψ       =>
      (∀ i,   models (drop i w) ψ)
    ∨ (∃ j, models (drop j w) φ ∧ ∀ k ≤ j, models (drop k w) ψ)
  | φ →ₗ ψ      => models w φ → models w ψ
  | r ◇→ φ      =>
    ∃ i, take (i + 1) w ⊫ r ∧ models (drop i w) φ
  | r ▫→ φ      =>
    ∀ i, take (i + 1) w ⊫ r → models (drop i w) φ
  | ⦃ r ⦄ =>
    (∃ i,   take i w ⊫ r) ∨ (∀ i > 0, ∃ x, take i w ++ x ⊫ r)
  | r^ω   => w ∈* r
notation:52 lhs:53 " |= " rhs:53 => RLTL.models lhs rhs

@[simp]
theorem expansion_until {φ ψ : RLTL α} :
  w |= (φ U ψ) ↔ w |= (ψ ∨ₗ (φ ∧ₗ X(φ U ψ))) := by
  simp[RLTL.models]
  apply Iff.intro
  . intro ⟨j,h1,h2⟩
    match j with
    | 0 => simp at h1; exact Or.inl h1
    | .succ j =>
      apply Or.inr ⟨h2 0 (by simp),j,h1,fun i hi => h2 i.succ (by linarith)⟩
  . intro h
    match h with
    | Or.inl h1 => exact ⟨0,h1,fun i hi => by simp at hi⟩
    | Or.inr ⟨h1,j,h2,h3⟩ =>
      exact ⟨j.succ,h2,fun i _ => match i with | 0 => h1 | .succ i => h3 i (by linarith)⟩

@[simp]
theorem expansion_release {φ ψ : RLTL α} :
  w |= (φ R ψ) ↔ w |= (ψ ∧ₗ (φ ∨ₗ X(φ R ψ))) := by
  simp[RLTL.models]
  apply Iff.intro
  . intro h
    match h with
    | Or.inl h1 => exact ⟨h1 0,Or.inr $ Or.inl (fun i => h1 i.succ)⟩
    | Or.inr ⟨j,h1,h2⟩ =>
      match j with
      | 0 => simp at h1 h2; exact ⟨h2,Or.inl h1⟩
      | .succ j =>
        exact ⟨h2 0 (by simp),Or.inr $ Or.inr ⟨j,h1,fun i hi => h2 i.succ (by linarith)⟩⟩
  . intro ⟨h1,h2⟩
    match h2 with
    | Or.inl h3 =>
      apply Or.inr ⟨0,by simp; exact h3,fun i hi => by simp at hi; subst hi; simp; exact h1⟩
    | Or.inr h3 =>
      match h3 with
      | Or.inl h4 =>
        apply Or.inl; intro j; match j with | 0 => simp; exact h1 | .succ j => exact h4 j
      | Or.inr ⟨j,h4,h5⟩ =>
        match j with
        | 0 => apply Or.inr ⟨1,h4,fun k h =>
                             match k with
                             | 0 => h1
                             | .succ k => by simp[Nat.succ_le_iff,nonpos_iff_eq_zero] at h
                                             subst h; exact h5 0 (by simp)⟩
        | .succ i =>
          apply Or.inr ⟨i.succ.succ,h4,fun k _ => match k with | 0 => h1 | .succ k => h5 k (by linarith)⟩

/-- An example of an algebraic rewrite rule: the existential suffix implication operator distributes over union. -/
theorem esi_distributivity {l r : ERE α} {φ : RLTL α} :
  w |= ((l ⋓ r) ◇→ φ) ↔ w |= (l ◇→ φ) ∨ w |= (r ◇→ φ) := by
  simp[RLTL.models, ERE.models]
  apply Iff.intro
  . intro ⟨i,h1,h2⟩
    match h1 with
    | Or.inl h1 => exact Or.inl ⟨i,h1,h2⟩
    | Or.inr h1 => exact Or.inr ⟨i,h1,h2⟩
  . intro h
    match h with
    | Or.inl ⟨i,h1,h2⟩ => exact ⟨i,Or.inl h1,h2⟩
    | Or.inr ⟨i,h1,h2⟩ => exact ⟨i,Or.inr h1,h2⟩

/-- An example of an algebraic rewrite rule: the universala suffix implication operator distributes over union. -/
theorem usi_distributivity {l r : ERE α} {φ : RLTL α} :
  w |= ((l ⋓ r) ▫→ φ) ↔ w |= (l ▫→ φ) ∧ w |= (r ▫→ φ) := by
  simp[RLTL.models, ERE.models]
  apply Iff.intro
  . intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  . intro h i hi
    match hi with
    | Or.inl hi => exact h.1 i hi
    | Or.inr hi => exact h.2 i hi

/-- The main theorem (Theorem 4 in the paper) proving derivation of the derivation rules for RLTL. -/
theorem derivation {φ : RLTL α} :
  a::w |= φ ↔ w |= (𝜕 φ) [a] :=
  match φ with
  | RLTL.Pred p => by
    simp [RLTL.models,evaluation,RLTL.derivative]
    by_cases h : denote p a
    . simp [h,RLTL.models]
    . simp [h,RLTL.models]
  | ¬ₗ φ => by
    simp [RLTL.models,RLTL.derivative,liftU]
    rw[derivation] -- inductive hypothesis
  | φ ∧ₗ ψ => by
    simp [RLTL.models,RLTL.derivative,liftB]
    rw[derivation,derivation] -- inductive hypothesis
  | φ ∨ₗ ψ => by
    simp [RLTL.models,RLTL.derivative,liftB]
    rw[derivation,derivation] -- inductive hypothesis
  | φ →ₗ ψ => by
    simp [RLTL.models,RLTL.derivative,liftB]
    rw[derivation,derivation] -- inductive hypothesis
  | X φ => by simp [RLTL.models, RLTL.derivative]
  | φ U ψ => by
    rw[expansion_until]
    simp [RLTL.models,RLTL.derivative,liftB]
    rw[derivation,derivation] -- inductive hypothesis
  | φ R ψ => by
    rw[expansion_release]
    simp [RLTL.models,RLTL.derivative,liftB]
    rw[derivation,derivation] -- inductive hypothesis
  | r ◇→ ψ => by
    simp only [RLTL.models,RLTL.derivative,liftB,liftB,liftU]
    by_cases g : denote (OneStep r) a
    . simp [g,RLTL.models]
      apply Iff.intro
      . intro ⟨i,h1,h2⟩
        match i with
        | 0       => exact Or.inl (derivation.mp h2) -- inductive hypothesis
        | .succ i => exact Or.inr ⟨i,equivalenceDer.mp h1,h2⟩
      . intro h
        match h with
        | Or.inl h1        =>
          exact ⟨0,equivalenceDer.mpr (denoteOneStep.mpr g),derivation.mpr h1⟩ -- inductive hypothesis
        | Or.inr ⟨i,h1,h2⟩ => exact ⟨i.succ,equivalenceDer.mpr h1,h2⟩
    . simp [g,RLTL.models]
      apply Iff.intro
      . intro ⟨i,h1,h2⟩
        match i with
        | 0       =>
          simp at h1; erw[←denoteOneStep] at g
          have := equivalenceDer (r:=r) (xs:=[]) (a:=a)
          rw[this] at h1
          contradiction
        | .succ i => exact ⟨i,equivalenceDer.mp h1,h2⟩
      . intro ⟨i,h1,h2⟩; exact ⟨i.succ,equivalenceDer.mpr h1,h2⟩
  | r ▫→ φ => by
    simp only [RLTL.models,RLTL.derivative,liftB,liftB,liftU]
    by_cases g : denote (OneStep r) a
    . simp[g,RLTL.models]
      apply Iff.intro
      . intro h
        have h1 := h 0 (equivalenceDer.mpr (denoteOneStep.mpr g))
        exact ⟨derivation.mp h1,fun i hi => h i.succ (equivalenceDer.mpr hi)⟩ -- inductive hypothesis
      . intro ⟨h1,h2⟩ i hi
        match i with
        | 0       => exact (derivation.mpr h1) -- inductive hypothesis
        | .succ i => exact h2 i (equivalenceDer.mp hi)
    . simp[g,RLTL.models]
      apply Iff.intro
      . intro h i hi; exact (h i.succ (equivalenceDer.mpr hi))
      . intro h i hi
        match i with
        | 0       => simp at hi; erw[←denoteOneStep] at g; rw[←equivalenceDer] at g; contradiction
        | .succ i => exact h i (equivalenceDer.mp hi)
  | ⦃ r ⦄ => by
    simp[RLTL.models,RLTL.derivative]
    by_cases g : nullable r
    . simp[g,RLTL.models]; exact Or.inl ⟨0,(equivalenceNull (r:=r)).mpr g⟩
    . simp[g,liftU,RLTL.models]
      apply Iff.intro
      . intro h
        match h with
        | Or.inl ⟨i,h1⟩ =>
          match i with
          | 0       => simp[equivalenceNull] at h1; contradiction
          | .succ i => apply Or.inl ⟨i,equivalenceDer.mp h1⟩
        | Or.inr h1 =>
          apply Or.inr
          intro i hi
          match i with
          | 0       => simp at hi -- contradiction
          | .succ i =>
            have ⟨k1,k2⟩ := h1 i.succ.succ (by linarith)
            exact ⟨k1,equivalenceDer.mp k2⟩
      . intro h
        match h with
        | Or.inl ⟨i,h1⟩ => exact Or.inl ⟨i.succ,equivalenceDer.mpr h1⟩
        | Or.inr h1 =>
          apply Or.inr; intro i hi
          match i with
          | 0       => simp at hi -- contradiction
          | .succ i =>
            match i with
            | 0 =>
              have ⟨j1,j2⟩ := h1 1 (by linarith)
              exact ⟨(Stream'.take 1 w ++ j1),equivalenceDer.mpr j2⟩
             | .succ i =>
               have ⟨j1,j2⟩ := h1 i.succ (by linarith)
               exact ⟨j1,equivalenceDer.mpr j2⟩
  | r^ω => by
    simp[RLTL.models,RLTL.derivative,liftB,liftU]
    by_cases g : denote (OneStep r) a
    . simp[g,RLTL.models]
      apply Iff.intro
      . intro ⟨deltas,proof⟩
        have h1 := charOmegaDrop proof
        by_cases p : head deltas = 0
        . rw[p,tail_eq_drop] at h1; apply Or.inl ⟨tail deltas,h1⟩
        . match hp : get deltas 0 with
          | 0 => contradiction
          | .succ n =>
            have gg2 := proof 0; simp[hp] at gg2
            erw[←Stream'.head_drop,Stream'.drop_zero] at hp
            rw[hp,drop_succ] at h1
            apply Or.inr ⟨n,equivalenceDer.mp gg2,tail deltas,h1⟩
      . intro h
        match h with
        | Or.inl ⟨deltas,h2⟩ => exact ⟨0::deltas,charOmegaCons h2 (equivalenceDer.mpr (denoteOneStep.mpr g))⟩
        | Or.inr ⟨i,h1,⟨deltas,proof⟩⟩ =>
          have gg := charOmegaCons proof (equivalenceDer.mpr h1)
          simp[cons_append_stream,append_take_drop] at gg
          exact ⟨i.succ::deltas,gg⟩
    . simp[g,RLTL.models]
      apply Iff.intro
      . intro ⟨deltas,h1⟩
        have h2 := charOmegaHead h1
        match hp : head deltas with
        | 0 => simp[hp] at h2; erw[←denoteOneStep] at g; rw[←equivalenceDer] at g; contradiction
        | .succ n =>
          simp[equivalenceDer,hp] at h2
          have t := charOmegaDrop h1; rw[hp,drop_succ] at t; exact ⟨n,h2,tail deltas,t⟩
      . intro ⟨i,pr,deltas,proof⟩
        erw[←append_take_drop (i+1) w,←cons_append_stream]
        exact ⟨length (take (i + 1) w)::deltas,charOmegaCons proof (equivalenceDer.mpr pr)⟩
