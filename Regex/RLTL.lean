import Regex.ERE
import Regex.OmegaLanguage
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Init.Data.Bool
import Mathlib.Data.Stream.Init

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
  | .Pred a => Node a (Leaf (Pred ⊤)) (Leaf (Pred ⊥))
  | ¬ₗ φ    => lift_unary (¬ₗ ·) (derivative φ)
  | φ ∧ₗ ψ  => lift_binary (· ∧ₗ ·) (derivative φ) (derivative ψ)
  | φ ∨ₗ ψ  => lift_binary (· ∨ₗ ·) (derivative φ) (derivative ψ)
  | X φ     => Leaf φ
  | φ U ψ   =>
    let rhs := lift_binary (· ∧ₗ ·) (derivative φ) (Leaf (φ U ψ))
    lift_binary (· ∨ₗ ·) (derivative ψ) rhs
  | φ R ψ   =>
    let rhs := lift_binary (· ∨ₗ ·) (derivative φ) (Leaf (φ R ψ))
    lift_binary (· ∧ₗ ·) (derivative ψ) rhs
  | φ →ₗ ψ  => lift_binary (· →ₗ ·) (derivative φ) (derivative ψ)
  | r ∷ φ  =>
    let lhs := Node (OneStep r) (derivative φ) (Leaf (Pred ⊥))
    lift_binary (· ∨ₗ ·) lhs (lift_unary (· ∷ φ) (δ r))
  | r :> φ  =>
    let lhs := Node (OneStep r) (derivative φ) (Leaf (Pred ⊤))
    lift_binary (· ∧ₗ ·) lhs (lift_unary (· :> φ) (δ r))
  | ⦃ r ⦄   =>
    if nullable r then
      Leaf (Pred ⊤)
    else
      lift_unary (⦃ . ⦄) (δ r)
  | r^ω     =>
    let lhs := lift_binary (· ∧ₗ ·) (derivative (Pred (OneStep r)))
                                    (Leaf r^ω)
    lift_binary (· ∨ₗ ·) lhs (lift_unary (· ∷ X (r^ω)) (δ r))
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
  | r ∷ φ  =>
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
                                             subst h
                                             exact h5 0 (Nat.zero_le 0)⟩
        | .succ i =>
          apply Or.inr ⟨i.succ.succ,h4,
                        λ k _ =>
                        match k with
                        | 0 => h1
                        | .succ k => h5 k (by linarith)⟩

/-- An example of an algebraic rewrite rule: the existential suffix implication operator distributes
    over union. -/
theorem esi_distributivity {l r : ERE α} {φ : RLTL α} :
  w |= ((l ⋓ r) ∷ φ) ↔ w |= (l ∷ φ) ∨ w |= (r ∷ φ) := by
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
    . simp [h, RLTL.models, modelsEBA, denote_top]
    . simp [h, RLTL.models, modelsEBA, denote_bot]
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
  | r ∷ ψ => by
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
    . simp [Stream'.take_succ_cons, evaluation, g, RLTL.models, modelsEBA, denote_bot, false_or]
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
    . simp [Stream'.take_succ_cons, evaluation, g, RLTL.models, modelsEBA, denote_top, true_and]
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
    . simp [g, RLTL.models, modelsEBA, denote_top, iff_true]
      exact Or.inl ⟨0,(equivalenceNull (r:=r)).mpr g⟩
    . simp [g, liftU, RLTL.models, gt_iff_lt]
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
    simp only [RLTL.models, RLTL.derivative, liftB, evaluation, liftU, tail_drop']
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
    . simp [g, RLTL.models, modelsEBA, denote_bot, false_and, false_or]
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


/-- xs ≺ ys means that xs is a non-empty proper prefix of xs. -/
@[simp]
def isProperPrefix (xs ys : List σ) := ∃ (i : ℕ), xs = List.take i ys ∧ xs ≠ ys
infixr:40 " ≺ "  => isProperPrefix

/-- r is a prefix-free language. -/
@[simp]
def prefixFree (r : ERE α) : Prop :=
  ∀ {xs ys}, xs ⊫ r ∧ ys ⊫ r → ¬ ys ≺ xs

theorem prefix_unique {r : ERE α} (h : prefixFree r)
  (h1 : Stream'.take i w ⊫ r) (hj : Stream'.take j w ⊫ r) : j = i := by
  by_cases g : i < j -- Stream'.take i w is a proper prefix of Stream'.take j w
  . simp at h
    have contra := (h hj h1) i (by simp[min_def, g]; have gg := Nat.lt_le_asymm g; simp[gg])
    have obv : (Stream'.take i w).length < (Stream'.take j w).length := by
      simp only [Stream'.length_take]; exact g
    simp [contra] at obv
  . simp only [not_lt] at g
    match Nat.eq_or_lt_of_le g with
    | Or.inl g1 => exact g1
    | Or.inr g1 =>
      simp at h
      have contra := (h h1 hj) j (by simp[min_def, g])
      have obv : (Stream'.take j w).length < (Stream'.take i w).length := by
        simp only [Stream'.length_take]; exact g1
      simp [contra] at obv

theorem unique_initial_match {r : ERE α} (h : prefixFree r) :
  w |= (r ∷ Pred ⊤) ↔ ∃! i₀, take (i₀ + 1) w ⊫ r := by
  simp only [RLTL.models, modelsEBA, Stream'.get_drop, zero_add, denote_top, and_true]
  apply Iff.intro
  . intro ⟨i,h1⟩; exists i; exists h1
    intro j hj
    apply (add_left_inj 1 (b:=j) (c:=i)).mp (prefix_unique h h1 hj)
  . intro ⟨i₀,h1,_⟩; exists i₀

theorem unique_continuation {r : ERE α} (h : prefixFree r) :
  w |= (r* :> X (r ∷ Pred ⊤)) ↔
  -- j is unique for any i
  (∀ i, (Stream'.take (i + 1) w) ⊫ r* →
  (∃! j, (Stream'.take (j + 1) (Stream'.drop (i + 1) w) ⊫ r))) := by
  apply Iff.intro
  . intro h1 j hj
    unfold RLTL.models at h1
    have := h1 _ hj
    unfold RLTL.models at this; rw[unique_initial_match h] at this
    have ⟨m,hm1,hm2⟩ := this
    simp at hm1 hm2; exists m
  . intro h1 j hj
    unfold RLTL.models; rw[unique_initial_match h]
    have ⟨m,hm1,hm2⟩ := h1 _ hj
    simp at hm1 hm2; exists m; simp; exists hm1

-- j is a valid boundary in deltas
def IsBoundary (deltas : Delta) : Nat → Prop := λ j =>
  ∃ (i : Index), getWordStart deltas i = j + 1

theorem unique_boundary {r : ERE α} (rpf : prefixFree r) (p : IsDeltasOmegaLanguage w r deltas):
  ∀ (i j : Index), getWordStart deltas i = getWordStart deltas j → get deltas i = get deltas j := by
  intro i j h
  have h1 := p i
  have h2 := p j
  simp at h1 h2
  rw[h] at h1
  have := prefix_unique rpf h1 h2
  simp at this
  simp[this]

theorem lemma23 (h : as ++ bs = Stream'.take i w)
  : length bs ≤ i := by
    have := congrArg List.length h;
    simp at this
    linarith

theorem lemma23' (h : as ++ bs = Stream'.take i w)
  : length as ≤ i := by
    have := congrArg List.length h;
    simp at this
    linarith

theorem comp2 {as : List σ}
  (h : as ++ bs = Stream'.take i w)
  : as = Stream'.take (i - bs.length) w := by
  match eq:as with
  | [] => aesop
  | .cons a as =>
    simp at h
    have := congrArg List.tail h
    simp at this
    match i with
    | 0 => simp at h
    | i + 1 =>
      simp[Stream'.take_succ] at this
      have m := lemma23 this
      have := comp2 this (w := Stream'.tail w)
      subst this
      rw[Nat.succ_sub m]
      rw[Stream'.take_succ]
      simp
      simp[Stream'.take_succ] at h
      exact h.1

theorem regexOmegaClosure_ne {r : ERE α} (rpf : prefixFree r) :
  IsDeltasOmegaLanguage w r deltas → ¬ Stream'.take 0 w ⊫ r := by
  intro h em
  simp at h
  have := h 0; simp[Stream'.get] at this
  have uniq := prefix_unique rpf em this
  simp at uniq

theorem helper (h3 : xs ++ h1 = Stream'.take i w)  :
  h1 = Stream'.take (length h1) (Stream'.drop (length xs) w) := by
  have := congrArg (List.drop xs.length) h3
  simp at this
  subst this
  rw[Stream'.take_drop]
  simp
  rw[Nat.add_sub_cancel']
  exact lemma23' h3

theorem asdf
  (z : as ++ h1 = Stream'.take i w)
  : as.length = i - h1.length := by
  have := congrArg (List.drop as.length) z
  simp at this
  subst this
  simp
  rw[Nat.sub_sub_eq_min]
  simp
  exact lemma23' z

theorem maibi {r : ERE α} (rpf : prefixFree r)
  (p : IsDeltasOmegaLanguage w r deltas)
  (h : Stream'.take (i + 1) w ⊫ r⁽m⁾) :
  getWordStart deltas m = i + 1 :=
  match m with
  | 0 => by
    simp at h
    match i with
    | 0 => simp[Stream'.take] at h
    | i + 1 => simp[Stream'.take] at h
  | m + 1 => by
    have infoFromP := p m
    unfold repeat_cat at h
    have cat_swap {xs : List σ} :
      xs ⊫ (r ⬝ r⁽m⁾) ↔ xs ⊫ (r⁽m⁾ ⬝ r) := sorry
    have new := (cat_swap (xs:=Stream'.take (i + 1) w)).mp h
    clear h
    simp at infoFromP new
    let ⟨as,bs,h1,h2,h3⟩ := new
    match as with
    | [] =>
      simp at h3
      subst h3
      have a := p 0
      simp at a
      have cc := prefix_unique rpf a h2
      simp at cc
      subst cc
      simp
      have : m = 0 := by
        cases m; simp; simp at bs
        have em := regexOmegaClosure_ne rpf p
        simp_all
      subst this
      simp
    | .cons a as =>
      have zz := comp2 h3
      have h1lei : length h1 ≤ i := by
        have := congrArg List.length h3;
        simp at this
        linarith
      rw[Nat.succ_sub h1lei] at zz
      rw[zz] at bs
      have eq := maibi rpf p bs
      rw[getWordStart_end p]
      rw[eq]
      have minpo := helper h3
      have ga : (a :: as).length = i - h1.length + 1 := by
        have := asdf h3
        rw[Nat.succ_sub h1lei] at this
        simp at this
        simp
        exact this
      have : Stream'.get deltas m + 1 = length h1 :=
        prefix_unique rpf
          (w := Stream'.drop (getWordStart deltas m) w)
          (by rw[eq];
              rw[←ga]
              rw[←minpo];
              exact h2)
          infoFromP
      rw[this]
      rw[←Nat.sub_add_comm h1lei]
      rw[Nat.sub_add_cancel]
      linarith

theorem exists_boundary {r : ERE α} (rpf : prefixFree r)
  (p : IsDeltasOmegaLanguage w r deltas)
  (h : Stream'.take (i + 1) w ⊫ r*) :
  IsBoundary deltas i := by
  unfold IsBoundary
  simp only [ERE.models] at h
  let ⟨m,hm⟩ := h
  clear h
  have := p m -- there are m matches (m lengths stored in deltas)
  simp at this
  exists m
  apply maibi rpf p hm

theorem prefixFree_equiv  {r : ERE α} (rpf : prefixFree r) :
  w |= r^ω → w |= (r* :> X(r ∷ Pred ⊤)) := by
  intro h
  simp_rw[unique_continuation rpf]
  simp at h
  let ⟨deltas,proof⟩ := h
  clear h
  intro i hi
  have ⟨j,hj⟩ := exists_boundary rpf proof hi
  have := proof j
  simp only at this
  rw[←hj]
  exists get deltas j
  simp
  exists this
  intro k hk
  have c := prefix_unique rpf this hk
  simp at c
  exact c

def amam {r : ERE α} : Decidable (w ⊫ r) := sorry


def deltaFromNothing
  (σ : Type u)
  (z : σ)
  (e : σ → ℕ)
  (d : σ → σ)
  : Index → ℕ := λ h =>
  match h with
  | 0 => e z
  | h + 1 => deltaFromNothing σ (d z) e d h

noncomputable def asdfasdf {r : ERE α} (rpf : prefixFree r)
  (h : w |= (r* :> X(r ∷ Pred ⊤))) :
    ∃ (a : Delta), IsDeltasOmegaLanguage w r deltas := by
  rw[unique_continuation rpf] at h
  unfold Delta
  exists
    deltaFromNothing
      (Σ' (m : Index) (wid : Nat),
          Stream'.take (m + 1) w ⊫ r*
        ∧ Stream'.take wid (Stream'.drop (m + 1) w) ⊫ r*)
      sorry
      (λ ⟨r,m,o⟩ => m)
      (λ ⟨p1,p2,p3,p4⟩ =>
        sorry
      )
  sorry

  -- intro idx
  -- unfold Index at idx
  -- match idx with
  -- | 0 =>
  --   have := h 0
  --   simp only [zero_add, ERE.models.eq_6, forall_exists_index] at this
  --   sorry
  -- | idx + 1 =>
  --   have := h idx
  --   match amam (w := Stream'.take (idx + 1) w) (r := r*) with
  --   | .isFalse z => sorry
  --   | .isTrue m =>
  --     have ytr := this m
  --     sorry


theorem prefixFree_equiv' {r : ERE α} (rpf : prefixFree r) :
  w |= (r* :> X(r ∷ Pred ⊤)) → w |= r^ω := by
  intro h
  unfold RLTL.models
  unfold InOmegaLanguage
  exists asdfasdf rpf h
  sorry





 /-
           abcdefghijklmopqrstuvwxyzeqoiwjdoihs...
           ^^^^^^^         ^^^^^^^      ^^^^^
                  ^^^^^^^^|       ^^^^^^
                          |
                r*
           -/
/-

  i₀ = 6
  take (i₀ + 1) w = abcdefg
     0123456789
  w = abcdefghijklmopqrstuvwxyz...
      ^^^^^^^        ^^^^^^^^
         r   |^^^^^^^        ^^

  1. i_0_in : take (i₀ + 1) w ⊫ r
  2. i_0_uniq : ∀ y, take (y + 1) w ⊫ r → y = i₀
-/

-- theorem deffer {r : ERE α} (rpf : prefixFree r) :
--   w |= (r* :> X(r ∷ Pred ⊤)) →
--     ∃ (as : Stream' ℕ),  :=


-- mutual
--   theorem deffer {r : ERE α} (rpf : prefixFree r) (h : w |= (r* :> X(r ∷ Pred ⊤))) (n : Nat) :
--     Lower Nat := by
--     match n with
--     | 0 =>
--       sorry
--     | n + 1 =>
--       have previousSize : Nat := sorry --prefixFree_equ rpf h n
--       have previousLength := deffer rpf h n
--       simp_rw[unique_continuation rpf] at h
--       -- by_cases g : (Stream'.take (n + 1) w ⊫ r*)
--       -- . have ⟨j,hj⟩ := h n g
--       --   sorry
--       -- . sorry
--       sorry
--   theorem prefixFree_equ_correct {r : ERE α} (rpf : prefixFree r)
--     (hyp : w |= (r* :> X(r ∷ Pred ⊤))) :
--     IsDeltasOmegaLanguage w r (deffer rpf hyp) :=
--     sorry
-- end

variable [∀ {xs : List σ} {r : ERE α}, Decidable (xs ⊫ r)]

inductive Lower (α : Type) : Prop where
| Base (value : α) : Lower α
open Lower

-- @[simp]
-- def getWordStart2 (w : Stream' Nat) (i : Nat) : Nat :=
--   match i with
--   | 0 => 0
--   | .succ i => getWordStart2 (tail w) i + (head w + 1)


-- @[simp]
-- def IsDeltasOmegaLanguage2 (w : Stream' σ) (r : ERE α) (deltas : Stream' ℕ) : Prop :=
--   ∀ (i : ℕ),                            -- for all starting indices (of all subwords)
--     let start := getWordStart2 deltas i  -- get the starting index of the subword
--     let len := get deltas i + 1         -- get the length of the subword
--     take len (drop start w) ⊫ r         -- check that it is in the language of r

-- def InOmegaLanguage2 (w : Stream' σ) (r : ERE α) : Prop :=
--   ∃ (deltas : Stream' (Lower Nat)), IsDeltasOmegaLanguage2 w r deltas


def next_pos {w : Stream' σ} {r : ERE α} (init : Nat) (n : Nat)
  (rest : ∀ (i : ℕ), Stream'.take (i + 1) w ⊫ r* → ∃! j, Stream'.take (j + 1) (Stream'.drop (i + 1) w) ⊫ r) :
  Lower Nat :=
  match n with
  | 0     =>
    Base init
  | n + 1 =>
    if h : (Stream'.take (n + 1) w ⊫ r*) then
      (by have ⟨j,h1,h2⟩ := rest n h;
          exact Base j)
    else
      sorry



theorem prefixFree_equiv {r : ERE α} (rpf : prefixFree r) :
  w |= ((r ∷ Pred ⊤) ∧ₗ (r* :> X(r ∷ Pred ⊤))) → w |= r^ω := by
  intro h
  unfold RLTL.models at h
  simp_rw[unique_initial_match rpf] at h
  simp_rw[unique_continuation rpf] at h
  let ⟨⟨i₀,i₀_in,i₀_uniq⟩,rest⟩ := h
  clear h
  simp only [RLTL.models]
  have := fun i => next_pos i₀ i rest
  exact ⟨Stream'.iterate (α := Nat) sorry i₀,
         fun i => by simp; sorry⟩


-- #check Classical.choice
-- theorem prefixFree_equiva {r : ERE α} (rpf : prefixFree r) :
--   w |= (r* :> X(r ∷ Pred ⊤)) → w |= r^ω := by
--   contrapose!
--   intro p
--   intro a
--   simp_rw[unique_continuation rpf] at a
--   simp at p; unfold InOmegaLanguage at p
--   simp only [IsDeltasOmegaLanguage, not_exists, not_forall] at p

--   sorry

  -- simp[Classical.contrapositive]
  -- simp_rw[unique_continuation rpf]
  -- intro h
  -- simp
  -- have deltas : Nat → Nat := by
  --   intro n
  --   ---have := h 0 (sorry)
  --   match n with
  --   | 0 => sorry --exact h
  --   | n + 1 =>
  --     exact deltas n
  --     -- by_cases g : (Stream'.take (n + 1) w ⊫ r*)
  --     -- . have ⟨j,hj⟩ := h n g
  --     --   sorry
  --     -- . sorry
  -- exact ⟨by intro i
  --           have mimo : ∃ (m : Nat), sorry := sorry
  --           let ⟨r,i⟩ := mimo
  --           sorry,by simp; sorry⟩


-- theorem prefixFree_equiv {r : ERE α} (rpf : prefixFree r) :
--   w |= ((r ∷ Pred ⊤) ∧ₗ (r* :> X(r ∷ Pred ⊤))) → w |= r^ω := by
--   unfold RLTL.models
--   simp_rw[unique_initial_match rpf]
--   simp_rw[unique_continuation rpf]
--   intro ⟨⟨i₀,i₀_in,i₀_uniq⟩,rest⟩
--   simp at i₀_in i₀_uniq
--   simp[InOmegaLanguage]
--   -- deltas(0) = i₀ + 1
--   -- deltas(n + 1) = n + 1 + j
--   have deltas : Nat → Nat := by
--     intro n
--     match n with
--     | 0 => exact i₀ + 1
--     | n + 1 =>
--       by_cases g : (Stream'.take (n + 1) w ⊫ r*)
--       . have := rest n g
--         sorry
--       . sorry
--   sorry

-- theorem prefixFree_equiv {r : ERE α} (rpf : prefixFree r) :
--   w |= r^ω ↔ w |= ((r ∷ Pred ⊤) ∧ₗ (r* :> X(r ∷ Pred ⊤))) := by
--   unfold RLTL.models
--   simp_rw[unique_initial_match rpf]
--   simp_rw[unique_continuation rpf]
--   apply Iff.intro
--   . sorry
--   . intro ⟨⟨first,first_in,first_uniq⟩,rest⟩
--     simp at first_in first_uniq
--     -- ∀ n, n.succ * first + n
--     have ⟨j1,a,a1⟩ := rest (first + 0) (by simp; exists 1; simp; exact first_in)
--     have ⟨j2,b,b1⟩ := rest (first + first + 1)
--                 (by simp; exists 2; simp; exists (Stream'.take (first + 1) w)
--                     exists first_in; exists (Stream'.take (first + 1) w)
--                     exists first_in; sorry)
--     have ⟨j3,c,c1⟩ := rest (first + first + first + 1 + 1)
--                   (by simp; exists 3; simp; exists (Stream'.take (first + 1) w)
--                       exists first_in; exists (Stream'.take (first + 1) w)
--                       exists first_in; exists (Stream'.take (first + 1) w)
--                       exists first_in; sorry)
--     simp at a b c
--     -- simp[InOmegaLanguage]
--     sorry

-- first
-- intro in_omega
--     simp only [InOmegaLanguage] at in_omega
--     let ⟨deltas,proof⟩ := in_omega; clear in_omega
--     exact ⟨⟨Stream'.get deltas 0,proof 0,
--             fun k hk => by
--             have := prefix_unique rpf (proof 0) hk
--             simp at this
--             exact this⟩,
--            fun m hm => by
--             -- simp at hm
--             -- let ⟨n + 1,hn⟩ := hm
--             -- have := charOmegaDrop proof

--             sorry⟩
