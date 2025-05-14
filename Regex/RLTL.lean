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
    . have := ERE.derivation.mpr $ denoteOneStep.mpr g
      simp only [g, ↓reduceIte, RLTL.models, modelsEBA, denote_top, true_and]
      apply Iff.intro
      . intro h
        simp_rw[←ERE.derivation]
        clear g
        let ⟨ws,p⟩ := h
        have ⟨a1 + 1,a2,a3,a4⟩ := base_case' p
        let ⟨p1,p2⟩ := p
        match a1 with
        | 0 =>
          simp at a4
          apply Or.inl
          unfold InOmegaLanguage
          exists (fun i => ws (i + 1))
          exists a4
          intro i hi
          simp at hi a3
          have ⟨len,k1,k2,k3⟩ := p2 _ hi
          exists len
          exists k1
          rw[Stream'.drop_succ,Stream'.tail_cons] at k2
          exists k2
          dsimp; rw[Nat.add_assoc,Nat.add_comm len 1,←Nat.add_assoc]
          exact k3
        | a1 + 1 =>
          apply Or.inr
          exists a1
          simp at a3
          exists a3
          exists (fun i => ws (a1 + i + 1 + 1))
          exists (by simp; exact a4)
          intro i hi
          have ⟨len,k1,k2,k3⟩ := p2 _ hi
          exists len
          exists k1
          rw[Stream'.drop_succ,Stream'.tail_cons] at k2
          simp
          rw[Nat.add_assoc,Nat.add_comm 1 i,←Nat.add_assoc]
          exists k2
          have : (a1 + i + 1 + 1 + len) = (a1 + (i + len) + 1 + 1) := by linarith
          rw[←this]
          exact k3
      . intro h
        match h with
        | Or.inl h1 => apply concat_stream (by simp) this h1
        | Or.inr ⟨i,hi,hi1⟩ =>
          clear h
          rw[←ERE.derivation] at hi
          have := concat_stream (by simp) hi hi1
          rw[Stream'.cons_append_stream] at this
          simp at this
          exact this
    . simp only [gt_iff_lt, g, Bool.false_eq_true, ↓reduceIte, models,
      modelsEBA, denote_bot, false_and, Stream'.drop_drop, false_or]
      erw [←denoteOneStep, ←ERE.derivation] at g
      apply Iff.intro
      . intro h
        simp_rw[←ERE.derivation]
        unfold InOmegaLanguage at h
        let ⟨vect,isB⟩ := h
        let ⟨m + 1,_,k, mi⟩ := base_case' isB
        simp only [IsBound, gt_iff_lt] at isB
        let ⟨i,hi⟩ := isB
        clear h isB
        match m with
        | 0 => contradiction
        | m + 1 =>
          exists m
          simp at k
          exists k
          exists λ j => vect (j + m + 1 + 1)
          exists (by simp; exact mi)
          intro i hyp
          have ⟨o1,o2,o3,o4⟩ := hi (i + m + 1 + 1) hyp
          rw[Stream'.drop_succ,Stream'.tail_cons] at o3
          exists o1
          exists (by simp; exact o2)
          exact ⟨by rw[Stream'.drop_drop, Nat.add_comm, ←Nat.add_assoc]; exact o3,
                 by simp only
                    have : i + m + 1 + 1 + o1 = i + o1 + m + 1 + 1 := by linarith
                    rw[←this]
                    exact o4⟩
      . intro ⟨i,hi,ss⟩
        rw[←ERE.derivation] at hi
        have := concat_stream (by simp) hi ss
        rw[Stream'.cons_append_stream] at this
        rw[Stream'.append_take_drop ] at this
        exact this

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

theorem lemma23 (h : as ++ bs = Stream'.take i w)
  : length as ≤ i := by
    have := congrArg List.length h;
    simp at this
    linarith

theorem ufff_cat  {r : ERE α} (rpf : prefixFree r) (isBC : IsBound w r isBound)
  (m : Stream'.take i w ⊫ r⁽k⁾) : isBound i = true := by
  let ⟨b1,b2⟩ := isBC
  match k with
  | 0 =>
    match i with
    | 0 => exact b1
    | i + 1 => simp[Stream'.take_succ] at m
  | k + 1 =>
    unfold repeat_cat at m
    have cat_swap : Stream'.take i w ⊫ (r⁽k⁾ ⬝ r) := equiv_repeat_cat_cat.mpr m
    simp at cat_swap
    let ⟨m1,m2,m3,m4,m5⟩ := cat_swap
    have cong1 := congrArg (List.take m1.length) m5
    simp at cong1
    rw[cong1] at m2
    have := ufff_cat rpf isBC m2
    rw[Nat.min_eq_right (lemma23 m5)] at this
    have ⟨k1,k2,k3,k4⟩ := b2 _ this
    have congL := congrArg List.length m5
    simp at congL
    have : k1 = m3.length := by
      have cong2 := congrArg (List.drop m1.length) m5
      simp at cong2
      rw[cong2] at m4
      rw[←congL] at m4
      rw[←Stream'.take_drop] at m4
      exact prefix_unique rpf m4 k3
    rw[←congL]
    rw[this] at k4
    exact k4


theorem ufff {r : ERE α} (rpf : prefixFree r) (h : IsBound w r isBound)
  (m : Stream'.take i w ⊫ r*) : isBound i = true := by
  simp[ERE.models] at m
  let ⟨k,m⟩ := m
  exact ufff_cat rpf h m

theorem prefixFree_equiv  {r : ERE α} (rpf : prefixFree r) :
  w |= r^ω → w |= (r* :> X(r ∷ Pred ⊤)) := by
  intro ⟨isBound,corr@⟨b0,h0⟩⟩
  simp_rw[unique_continuation rpf]
  intro i z
  have := ufff rpf corr z
  have ⟨t+1,t2,t3,_⟩ := h0 (i + 1) this
  exact ⟨t, t3,
    by intro y
       intro m
       have c := prefix_unique rpf t3 m
       simp at c
       exact c⟩

theorem prefixFree_equiv1 {r : ERE α} (rpf : prefixFree r) :
  w |= r^ω → w |= ((r ∷ Pred ⊤) ∧ₗ (r* :> X(r ∷ Pred ⊤))) := by
  intro ⟨isBound,corr@⟨b0,h0⟩⟩
  unfold RLTL.models
  simp_rw[unique_initial_match rpf]
  simp_rw[unique_continuation rpf]
  apply And.intro
  . have ⟨g1 + 1,g2,g3⟩ := base_case' corr
    exists g1
    simp
    exists g3.1
    intro y hy
    have := prefix_unique rpf g3.1 hy
    simp at this
    exact this
  . intro i z
    have := ufff rpf corr z
    have ⟨t+1,t2,t3,_⟩ := h0 (i + 1) this
    exact ⟨t, t3,
      by intro y
         intro m
         have c := prefix_unique rpf t3 m
         simp at c
         exact c⟩

theorem prefixFree_equiv' {r : ERE α} (rpf : prefixFree r) :
  w |= ((r ∷ Pred ⊤) ∧ₗ (r* :> X(r ∷ Pred ⊤))) → w |= r^ω := by
  intro h
  unfold RLTL.models at h
  simp_rw[unique_initial_match rpf] at h
  simp_rw[unique_continuation rpf] at h
  let ⟨⟨len,lem,ler⟩,leg⟩ := h
  unfold RLTL.models
  exists
    (λ j => decide (Stream'.take j w ⊫ r*))
  apply And.intro
  . simp
    exists 0
    dsimp
    simp
  . intro i m
    match i with
    | 0 =>
      simp;
      exists len + 1
      exists (by simp)
      exists lem
      exists 1
      dsimp at lem
      simp
      exact lem
    | i + 1 =>
      simp only [decide_eq_true_eq] at m
      have ⟨uj,jc1,jc2⟩ := leg i m
      exists uj + 1
      exists (by simp)
      exists jc1
      simp only [decide_eq_true_eq]
      have asd := semmm' m jc1
      rw[Stream'.take_add]
      exact asd

theorem prefixFree_equiv_final {r : ERE α} (rpf : prefixFree r) :
  w |= r^ω ↔ w |= ((r ∷ Pred ⊤) ∧ₗ (r* :> X(r ∷ Pred ⊤))) :=
  ⟨prefixFree_equiv1 rpf, prefixFree_equiv' rpf⟩
