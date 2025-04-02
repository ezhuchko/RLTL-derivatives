import Regex.TTerm
import Regex.Metrics

/-!
# ERE derivation

Contains match semantics and derivation rules for ERE, as well as the main
derivation theorem.

The specification of the matching relation follows the same approach
of language-based matching. The semantics is provided directly as an inductive predicate, in Prop.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List TTerm ERE EffectiveBooleanAlgebra

/-- The `nullable` function checks if the language of a given regex contains the empty
    string i.e. `ε ∈ L(r) ?`. -/
@[simp]
def nullable : ERE α → Bool
  | ε          => true
  | ERE.Pred _ => false
  | l ⋓ r      => nullable l || nullable r
  | l ⋒ r      => nullable l && nullable r
  | l ⬝ r      => nullable l && nullable r
  | _*         => true
  | ~ r        => !nullable r
  | _ : _      => false

@[simp]
def OneStep' : TTerm α (ERE α) → α
  | Leaf r     => if nullable r then ⊤ else ⊥
  | Node α f g => (α ⊓ OneStep' f) ⊔ (αᶜ ⊓ OneStep' g)

/-- Computes the symbolic derivatives of a given regex. The resulting `TTerm⟨α,ERE α⟩`
    encodes the transition behaviour of the `derivative` function.  -/
@[simp]
def ERE.derivative : ERE α → TTerm α (ERE α)
  | ε          => .pure (Pred ⊥)
  | ERE.Pred b => Node b (.pure ε) (.pure (Pred ⊥))
  | l ⋓ r      => lift_binary (· ⋓ ·) (derivative l) (derivative r)
  | l ⋒ r      => lift_binary (· ⋒ ·) (derivative l) (derivative r)
  | l ⬝ r      =>
    if nullable l then
      lift_binary (· ⋓ ·) (lift_binary (· ⬝ ·) (derivative l) (.pure r))
                          (derivative r)
    else
      lift_binary (· ⬝ ·) (derivative l) (.pure r)
  | r *   => lift_binary (· ⬝ ·) (derivative r) (.pure r*)
  | ~ r   => lift_unary (~ ·) (derivative r)
  | l : r =>
    let lhs := Node (OneStep' (derivative l)) (derivative r) (.pure (Pred ⊥))
    lift_binary (· ⋓ ·) lhs (lift_unary (· : r) (derivative l))
prefix:max " δ " => ERE.derivative

/-- The match semantics of ERE are formalised using the models relation. -/
@[simp]
def ERE.models (xs : List σ) (r : ERE α) : Prop :=
  match r with
  | ε          => xs = []
  | ERE.Pred p => ∃ c, xs = [c] ∧ c ⊨ p
  | l ⋓ r      =>
    have : star_metric l < (star_metric (l ⋓ r)) := star_metric_altL
    have : star_metric r < (star_metric (l ⋓ r)) := star_metric_altR
    models xs l ∨ models xs r
  | l ⋒ r      =>
    have : star_metric l < (star_metric (l ⋒ r)) := star_metric_interL
    have : star_metric r < (star_metric (l ⋒ r)) := star_metric_interR
    models xs l ∧ models xs r
  | l ⬝ r      =>
    ∃ (u₁ u₂ : List σ),
          have : star_metric l < (star_metric (l ⬝ r)) := star_metric_catL
          have : star_metric r < (star_metric (l ⬝ r)) := star_metric_catR
          models u₁ l
        ∧ models u₂ r
        ∧ u₁ ++ u₂ = xs
  | r *        =>
    ∃ (m : ℕ),
    have : star_metric (repeat_cat r m) < star_metric r* := star_metric_star
    models xs (repeat_cat r m)
  | ~ r        =>
    have : star_metric r < (star_metric (~ r)) := star_metric_neg
    ¬ models xs r
  | l : r      =>
    ∃ (u₁ u₂ : List σ) (c : σ),
          have : star_metric l < (star_metric (l : r)) := star_metric_catL
          have : star_metric r < (star_metric (l : r)) := star_metric_catR
          models (u₁ ++ [c]) l
        ∧ models (c::u₂) r
        ∧ u₁ ++ [c] ++ u₂ = xs
termination_by star_metric r
decreasing_by
  repeat assumption
notation:52 lhs:53 " ⊫ " rhs:53 => ERE.models lhs rhs

theorem predicate_nonEmpty {p : α}:
  ¬ [] ⊫ Pred p :=
  λ g => by
  let ⟨_,gfalse,_⟩ := g
  simp only at gfalse

theorem equivalenceNull {r : ERE α} :
  [] ⊫ r ↔ nullable r :=
  match r with
  | ε      => by simp only [models, nullable]
  | Pred p => by
    simp_rw [predicate_nonEmpty]
    simp only [nullable]
  | l ⋓ r  => by
    simp only [models, nullable, Bool.or_eq_true]
    apply or_congr equivalenceNull equivalenceNull -- inductive hypothesis
  | l ⋒ r  => by
    simp only [models, nullable, Bool.and_eq_true]
    apply and_congr equivalenceNull equivalenceNull -- inductive hypothesis
  | l ⬝ r  => by
    simp only [models, append_eq_nil, nullable, Bool.and_eq_true]
    simp_rw [←equivalenceNull (r:=l),←equivalenceNull (r:=r)] -- inductive hypothesis
    apply Iff.intro
    . intro ⟨xs,ys,h1,h2,eq1,eq2⟩; subst eq1 eq2; exact ⟨h1,h2⟩
    . intro ⟨h1,h2⟩; exact ⟨[],[],h1,h2,rfl,rfl⟩
  | r *    => by
    simp only [models, nullable, iff_true]
    exists 0
  | ~ r    => by
    simp only [models, nullable, Bool.not_eq_true']
    simp only [equivalenceNull, Bool.not_eq_true] -- inductive hypothesis
  | l : r  => by
    simp only [ERE.models, nullable, iff_false]
    simp only [append_assoc, singleton_append, append_eq_nil]
    intro ⟨_,_,_,_,_,_,hfalse⟩; exact hfalse

theorem denoteOneStep' {f : TTerm α (ERE α)} :
  [] ⊫ f [a] ↔ a ⊨ (OneStep' f) :=
  match f with
  | Leaf rr => by
    simp only [OneStep', evaluation, equivalenceNull, modelsEBA]
    by_cases h : nullable rr
    . simp only [h, ↓reduceIte, denote_top]
    . simp only [h, ↓reduceIte, denote_bot]
  | Node g g1 g2 => by
    by_cases h : denote g a
    . simp only [OneStep', evaluation, h, modelsEBA, denote_sup, denote_inf,
                 Bool.true_and, denote_compl, Bool.not_true, Bool.false_and,
                 Bool.or_false]
      apply denoteOneStep' -- inductive hypothesis
    . simp only [OneStep', evaluation, h, modelsEBA, denote_sup, denote_inf,
                 Bool.false_and, denote_compl, Bool.not_false, Bool.true_and,
                 Bool.false_or]
      apply denoteOneStep' -- inductive hypothesis

theorem denoteOneStep {r : ERE α} :
  [] ⊫ (δ r) [a] ↔ (a ⊨ OneStep' (δ r)) := by
  match δ r with
  | Leaf f =>
    simp only [evaluation, equivalenceNull, modelsEBA, OneStep']
    by_cases h : nullable f
    . simp only [h, ↓reduceIte, denote_top]
    . simp only [h, ↓reduceIte, denote_bot]
  | Node p f g =>
    simp only [evaluation, modelsEBA, OneStep', denote_sup,
               denote_inf, denote_compl, Bool.or_eq_true,
               Bool.and_eq_true, Bool.not_eq_true']
    match denote p a with
    | true =>
      apply Iff.intro
      . intro h
        simp only [true_and, false_and, or_false]
        apply denoteOneStep'.mp h
      . intro h
        match h with
        | Or.inl h1 =>
          simp only [true_and] at h1
          apply denoteOneStep'.mpr h1
        | Or.inr h1 =>
          simp only [false_and] at h1 -- contradiction
    | false =>
      apply Iff.intro
      . intro h; simp only [false_and, true_and, false_or]
        apply denoteOneStep'.mp h
      . intro h
        match h with
        | Or.inl h1 =>
          simp only [false_and] at h1 -- contradiction
        | Or.inr h1 =>
          simp only [true_and] at h1
          apply denoteOneStep'.mpr h1

theorem derives_Star {r : ERE α} (h : a :: xs ⊫ r⁽n⁾) :
  ∃ u₁, a::u₁ ⊫ r ∧ ∃ x, (∃ m, x ⊫ r⁽m⁾) ∧ u₁ ++ x = xs := by
  match n with
  | 0 => simp only [repeat_cat, models] at h
  | .succ n =>
    simp only [repeat_cat, models, exists_and_left] at h
    let ⟨u1,h1,u2,h2,h3⟩ := h
    match u1 with
    | [] =>
      simp only [nil_append] at h3; subst h3
      exact derives_Star h2 -- inductive hypothesis
    | .cons z zs =>
      match xs with
      | [] =>
        simp only [cons_append, cons.injEq, append_eq_nil] at h3
        let ⟨k1,k2,k3⟩ := h3
        subst k1 k2 k3
        simp only [append_eq_nil, exists_eq_right_right]
        exact ⟨h1,⟨n,h2⟩⟩
      | .cons x xs =>
        simp only [cons_append, cons.injEq] at h3
        let ⟨k1,k2⟩ := h3
        subst k1
        exact ⟨zs,h1,⟨u2,⟨n,h2⟩,k2⟩⟩

theorem ERE.derivation {r : ERE α} :
  a::xs ⊫ r ↔ xs ⊫ (δ r)[a] :=
  match r with
  | ε => by
    simp only [models, evaluation, modelsEBA,
               denote_bot, and_false, exists_false]
  | ERE.Pred p => by
    simp only [models, cons.injEq, modelsEBA, evaluation]
    by_cases h : denote p a
    . simp only [h, ↓reduceIte, models]
      apply Iff.intro
      . intro ⟨_,⟨_,x2⟩,_⟩; subst x2; rfl
      . intro h1; subst h1; exact ⟨a,⟨⟨rfl,rfl⟩,h⟩⟩
    . simp only [h, ↓reduceIte, models, modelsEBA,
                 denote_bot, and_false,
                 exists_false, iff_false, not_exists, not_and,
                 Bool.not_eq_true, and_imp, forall_eq', implies_true]
  | l ⋓ r => by
    simp only [ERE.models,evaluation,ERE.derivative]
    rw [ERE.derivation,ERE.derivation,liftB] -- inductive hypothesis
    simp only [models]
  | l ⋒ r => by
    simp only [ERE.models,evaluation,ERE.derivative]
    rw [ERE.derivation,ERE.derivation,liftB] -- inductive hypothesis
    simp only [models]
  | r * => by
    simp only [ERE.models,evaluation,ERE.derivative,liftB]
    simp only [exists_and_left]
    apply Iff.intro
    . intro ⟨n,g⟩
      let ⟨u1,h1,⟨h2,h3,h4⟩⟩ := derives_Star g
      rw [ERE.derivation] at h1 -- inductive hypothesis
      exact ⟨u1,h1,⟨h2,⟨h3,h4⟩⟩⟩
    . intro ⟨h1,h2,h3,⟨n,h4⟩,h5⟩; exists n.succ
      simp only [repeat_cat, models, exists_and_left]
      match n with
      | 0 =>
        simp only [repeat_cat, models] at h4
        subst h4
        simp only [append_nil] at h5
        simp only [repeat_cat]; subst h5
        simp only [models, exists_eq_left, append_nil, exists_eq_right]
        apply ERE.derivation.mpr h2 -- inductive hypothesis
      | .succ n =>
        simp only [repeat_cat] at h4
        simp only [repeat_cat]
        match h1 with
        | [] =>
          simp only [nil_append] at h5; subst h5
          exists [a]
          exists ERE.derivation.mpr h2 -- inductive hypothesis
          exists h3
        | .cons rr rs =>
          simp only [cons_append] at h5; subst h5
          exists (a::rr::rs)
          exists ERE.derivation.mpr h2 -- inductive hypothesis
          exists h3
  | ~ r => by
    simp only [models, derivative, liftU]
    rw [ERE.derivation] -- inductive hypothesis
  | l ⬝ r => by
    simp only [models, exists_and_left, derivative, TTerm.pure]
    by_cases g : nullable l
    . simp only [g, ↓reduceIte, liftB, evaluation, models, exists_and_left]
      apply Iff.intro
      . intro ⟨u,hu,⟨x,hv,hv1⟩⟩
        match u with
        | [] =>
          subst hv1
          apply Or.inr (ERE.derivation.mp hv) -- inductive hypothesis
        | .cons rr rs =>
          simp only [cons_append, cons.injEq] at hv1
          let ⟨k1,k2⟩ := hv1; subst k1
          apply Or.inl ⟨rs,ERE.derivation.mp hu,⟨x,hv,k2⟩⟩ -- inductive hypothesis
      . intro h1
        match h1 with
        | Or.inl ⟨u,hu,⟨x,hv,hv1⟩⟩ =>
          subst hv1; exact ⟨a::u,ERE.derivation.mpr hu,⟨x,hv,rfl⟩⟩ -- inductive hypothesis
        | Or.inr h3 =>
          exact ⟨[],equivalenceNull.mpr g,⟨a::xs,ERE.derivation.mpr h3,rfl⟩⟩ -- inductive hypothesis
    . simp only [g, ↓reduceIte, liftB, evaluation, models, exists_and_left]
      apply Iff.intro
      . intro ⟨h1,h2,⟨h3,h4,h5⟩⟩
        match h1 with
        | [] =>
          simp only [nil_append] at h5; subst h5
          rw [←equivalenceNull] at g; contradiction
        | .cons rr rs =>
          simp only [cons_append, cons.injEq] at h5
          let ⟨k1,k2⟩ := h5; subst k1
          exact ⟨rs,ERE.derivation.mp h2,⟨h3,h4,k2⟩⟩ -- inductive hypothesis
      . intro ⟨h1,h2,⟨h3,h4,h5⟩⟩
        exact ⟨a::h1,ERE.derivation.mpr h2, -- inductive hypothesis
               ⟨h3,h4,by simp only [cons_append, cons.injEq,true_and]; exact h5⟩⟩
  | l : r => by
    by_cases g : denote (OneStep' δ l) a = true
    . apply Iff.intro
      . intro h
        simp only [models, append_assoc, singleton_append] at h
        let ⟨u1,u2,d,h1,h2,h3⟩ := h
        match u1 with
        | [] =>
          simp only [nil_append, cons.injEq] at h1 h2 h3
          let ⟨k1,k2⟩ := h3; subst k1 k2
          simp only [derivative, liftB, TTerm.pure, liftU]
          simp only [evaluation, g, ↓reduceIte, models, append_assoc, singleton_append]
          apply Or.inl (ERE.derivation.mp h2) -- inductive hypothesis
        | a::as =>
          simp only [cons_append, cons.injEq] at h1 h2 h3
          let ⟨k1,_⟩ := h3; subst k1
          simp only [derivative, liftB, TTerm.pure,liftU]
          simp only [evaluation, g, ↓reduceIte, models, append_assoc, singleton_append]
          apply Or.inr ⟨as,u2,d,(ERE.derivation.mp h1),h2,h3.2⟩ -- inductive hypothesis
      . intro h
        simp only [models,g,derivative,liftB,TTerm.pure,liftU] at h
        simp only [evaluation, g, ↓reduceIte, append_assoc, singleton_append] at h
        match h with
        | Or.inl h1 =>
          unfold models; exists []; exists xs; exists a
          simp only [nil_append, singleton_append, and_true]
          exact ⟨ERE.derivation.mpr (denoteOneStep.mpr g),ERE.derivation.mpr h1⟩ -- inductive hypothesis
        | Or.inr ⟨u1,u2,d,h1,h2,h3⟩ =>
          unfold models; exists (a::u1); exists u2; exists d
          simp only [cons_append, append_assoc, singleton_append, cons.injEq, true_and]
          exact ⟨ERE.derivation.mpr h1,h2,h3⟩ -- inductive hypothesis
    . apply Iff.intro
      . intro h
        simp only [models, append_assoc, singleton_append] at h
        let ⟨u1,u2,d,h1,h2,h3⟩ := h
        match u1 with
        | [] =>
          simp only [derivative, liftB, TTerm.pure, liftU, g, models]
          simp only [nil_append, cons.injEq] at h1 h3
          let ⟨k1,k2⟩ := h3; subst k1
          rw [ERE.derivation] at h1 -- inductive hypothesis
          have := denoteOneStep (r:=l) (a:=d)
          unfold modelsEBA at this
          rw [this.mp h1] at g
          contradiction
        | a::as =>
          simp only [derivative, liftB, TTerm.pure, liftU, g, models]
          simp only [cons_append, cons.injEq] at h1 h3
          let ⟨k1,k2⟩ := h3; subst k1
          simp only [evaluation, append_assoc, singleton_append]
          rw [ERE.derivation] at h1 -- inductive hypothesis
          apply Or.inr ⟨as,u2,d,h1,h2,h3.2⟩
      . intro h
        simp only [derivative, TTerm.pure, liftB, liftU] at h
        simp only [evaluation, g, ↓reduceIte, models, modelsEBA,
                   denote_bot, and_false, exists_false, append_assoc,
                   singleton_append, false_or] at h
        let ⟨u1,u2,d,h1,h2,h3⟩ := h
        match u1 with
        | [] =>
          simp only [nil_append] at h1 h2 h3; subst h3
          simp only [models]
          rw [←ERE.derivation] at h1 -- inductive hypothesis
          exact ⟨[a],u2,d,h1,h2,rfl⟩
        | b::bs =>
          simp only [cons_append] at h1 h2 h3; subst h3
          simp only [models]
          rw [←ERE.derivation] at h1 -- inductive hypothesis
          exact ⟨a::b::bs,u2,d,h1,h2,
                 by simp only [cons_append, append_assoc, singleton_append]
                    simp only [nil_append]⟩

/-- Multi-step evaluation function for `ERE α`. -/
@[simp]
def ERE.multi_step : ERE α → List σ → ERE α
  | r, []    => r
  | r, a::as => multi_step ((δ r) [a]) as

theorem ERE.derivationMultiStep {r : ERE α} {u v : List σ} :
  v ⊫ multi_step r u ↔ u++v ⊫ r :=
  match u with
  | [] => Eq.to_iff rfl
  | a::as => by
    simp only [multi_step, cons_append]
    rw [ERE.derivation, derivationMultiStep]
